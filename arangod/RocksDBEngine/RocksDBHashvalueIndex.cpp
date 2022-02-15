////////////////////////////////////////////////////////////////////////////////
/// DISCLAIMER
///
/// Copyright 2014-2022 ArangoDB GmbH, Cologne, Germany
/// Copyright 2004-2014 triAGENS GmbH, Cologne, Germany
///
/// Licensed under the Apache License, Version 2.0 (the "License");
/// you may not use this file except in compliance with the License.
/// You may obtain a copy of the License at
///
///     http://www.apache.org/licenses/LICENSE-2.0
///
/// Unless required by applicable law or agreed to in writing, software
/// distributed under the License is distributed on an "AS IS" BASIS,
/// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
/// See the License for the specific language governing permissions and
/// limitations under the License.
///
/// Copyright holder is ArangoDB GmbH, Cologne, Germany
///
/// @author Jan Steemann
/// @author Daniel H. Larkin
/// @author Simon Grätzer
////////////////////////////////////////////////////////////////////////////////

#include "RocksDBHashvalueIndex.h"
#include "ApplicationFeatures/ApplicationServer.h"
#include "Aql/AstNode.h"
#include "Aql/SortCondition.h"
#include "Basics/StaticStrings.h"
#include "Basics/VelocyPackHelper.h"
#include "Containers/FlatHashMap.h"
#include "Containers/FlatHashSet.h"
#include "Indexes/SimpleAttributeEqualityMatcher.h"
#include "RocksDBEngine/RocksDBCollection.h"
#include "RocksDBEngine/RocksDBColumnFamilyManager.h"
#include "RocksDBEngine/RocksDBCommon.h"
#include "RocksDBEngine/RocksDBComparator.h"
#include "RocksDBEngine/RocksDBCuckooIndexEstimator.h"
#include "RocksDBEngine/RocksDBKeyBounds.h"
#include "RocksDBEngine/RocksDBPrimaryIndex.h"
#include "RocksDBEngine/RocksDBSettingsManager.h"
#include "RocksDBEngine/RocksDBTransactionCollection.h"
#include "RocksDBEngine/RocksDBTransactionMethods.h"
#include "RocksDBEngine/RocksDBTransactionState.h"
#include "StorageEngine/EngineSelectorFeature.h"
#include "Transaction/Helpers.h"
#include "Transaction/Methods.h"
#include "Utils/OperationOptions.h"
#include "VocBase/LogicalCollection.h"

#include <rocksdb/iterator.h>
#include <rocksdb/options.h>
#include <rocksdb/utilities/transaction.h>
#include <rocksdb/utilities/transaction_db.h>
#include <rocksdb/utilities/write_batch_with_index.h>

#include <velocypack/Iterator.h>
#include <velocypack/velocypack-aliases.h>

using namespace arangodb;

// .............................................................................
// recall for all of the following comparison functions:
//
// left < right  return -1
// left > right  return  1
// left == right return  0
//
// furthermore:
//
// the following order is currently defined for placing an order on documents
// undef < null < boolean < number < strings < lists < hash arrays
// note: undefined will be treated as NULL pointer not NULL JSON OBJECT
// within each type class we have the following order
// boolean: false < true
// number: natural order
// strings: lexicographical
// lists: lexicographically and within each slot according to these rules.
// ...........................................................................

namespace arangodb {

class RocksDBHashvalueIndexIterator final : public IndexIterator {
 private:
  friend class RocksDBHashvalueIndex;

 public:
  RocksDBHashvalueIndexIterator(LogicalCollection* collection,
                                transaction::Methods* trx,
                                arangodb::RocksDBHashvalueIndex const* index,
                                VPackSlice lookupValue,
                                ReadOwnWrites readOwnWrites)
      : IndexIterator(collection, trx, readOwnWrites),
        _index(index),
        _cmp(index->comparator()),
        _lookupValues(lookupValue),
        _hash(_lookupValues.slice().normalizedHash()),
        _bounds(RocksDBKeyBounds::HashvalueIndex(index->objectId(), _hash)),
        _rangeBound(_bounds.end()),
        _mustSeek(true),
        _mustCheckBounds(
            RocksDBTransactionState::toState(trx)->iteratorMustCheckBounds(
                collection->id(), readOwnWrites)) {
    TRI_ASSERT(index->columnFamily() ==
               RocksDBColumnFamilyManager::get(
                   RocksDBColumnFamilyManager::Family::HashvalueIndex));
  }

 public:
  char const* typeName() const override { return "rocksdb-hashvalue-iterator"; }

  /// @brief index does support rearming
  bool canRearm() const override { return true; }

  /// @brief rearm the index iterator
  bool rearmImpl(arangodb::aql::AstNode const* node,
                 arangodb::aql::Variable const* variable,
                 IndexIteratorOptions const& opts) override {
    TRI_ASSERT(node != nullptr);
    TRI_ASSERT(node->type == aql::NODE_TYPE_OPERATOR_NARY_AND);

    // this will be reused for multiple invocations of getValueAccess
    std::pair<arangodb::aql::Variable const*,
              std::vector<arangodb::basics::AttributeName>>
        paramPair;

    auto getValueAccess = [&](arangodb::aql::AstNode const* comp,
                              arangodb::aql::AstNode const*& access,
                              arangodb::aql::AstNode const*& value) -> bool {
      access = comp->getMember(0);
      value = comp->getMember(1);
      if (!(access->isAttributeAccessForVariable(paramPair) /*&&
            paramPair.first == reference*/)) {
        access = comp->getMember(1);
        value = comp->getMember(0);
        if (!(access->isAttributeAccessForVariable(paramPair) /*&&
              paramPair.first == reference*/)) {
          // Both side do not have a correct AttributeAccess, this should not
          // happen and indicates
          // an error in the optimizer
          TRI_ASSERT(false);
        }
        return true;
      }
      return false;
    };

    _lookupValues.clear();
    _lookupValues.openArray(true);

    for (auto const& field : _index->fields()) {
      size_t const n = node->numMembers();
      for (size_t i = 0; i < n; ++i) {
        arangodb::aql::AstNode const* comp = node->getMemberUnchecked(i);

        TRI_ASSERT(comp->numMembers() == 2);
        arangodb::aql::AstNode const* access = nullptr;
        arangodb::aql::AstNode const* value = nullptr;
        getValueAccess(comp, access, value);

        if (paramPair.second == field) {
          value->toVelocyPackValue(_lookupValues);
        }
      }
    }

    _lookupValues.close();

    _hash = _lookupValues.slice().normalizedHash();
    _bounds.reset(RocksDBEntryType::HashvalueIndexValue, _index->objectId(),
                  _hash);
    _rangeBound = _bounds.end();

    // sets _mustSeek
    resetImpl();
    TRI_ASSERT(_mustSeek);

    return true;
  }

  /// @brief Get the next limit many elements in the index
  bool nextImpl(LocalDocumentIdCallback const& cb, size_t limit) override {
    ensureIterator();
    TRI_ASSERT(_trx->state()->isRunning());
    TRI_ASSERT(_iterator != nullptr);

    if (limit == 0 || !_iterator->Valid() || outOfRange()) {
      // No limit no data, or we are actually done. The last call should have
      // returned false
      TRI_ASSERT(limit > 0);  // Someone called with limit == 0. Api broken
      // validate that Iterator is in a good shape and hasn't failed
      arangodb::rocksutils::checkIteratorStatus(_iterator.get());
      return false;
    }

    TRI_ASSERT(limit > 0);

    do {
      TRI_ASSERT(_index->objectId() == RocksDBKey::objectId(_iterator->key()));

      VPackSlice key = RocksDBValue::hashvalueIndexedVPack(_iterator->value());
      if (arangodb::basics::VelocyPackHelper::compare(
              key, _lookupValues.slice(), true, nullptr) == 0) {
        cb(RocksDBKey::indexDocumentId(_iterator->key()));
      }

      if (!advance()) {
        // validate that Iterator is in a good shape and hasn't failed
        arangodb::rocksutils::checkIteratorStatus(_iterator.get());
        return false;
      }

      --limit;
      if (limit == 0) {
        return true;
      }
    } while (true);
  }

  bool nextCoveringImpl(CoveringCallback const& cb, size_t limit) override {
    ensureIterator();
    TRI_ASSERT(_trx->state()->isRunning());
    TRI_ASSERT(_iterator != nullptr);

    if (limit == 0 || !_iterator->Valid() || outOfRange()) {
      // No limit no data, or we are actually done. The last call should have
      // returned false
      TRI_ASSERT(limit > 0);  // Someone called with limit == 0. Api broken
      // validate that Iterator is in a good shape and hasn't failed
      arangodb::rocksutils::checkIteratorStatus(_iterator.get());
      return false;
    }

    TRI_ASSERT(limit > 0);

    do {
      TRI_ASSERT(_index->objectId() == RocksDBKey::objectId(_iterator->key()));

      VPackSlice key = RocksDBValue::hashvalueIndexedVPack(_iterator->value());

      if (arangodb::basics::VelocyPackHelper::compare(
              key, _lookupValues.slice(), true, nullptr) == 0) {
        LocalDocumentId const documentId(
            RocksDBKey::indexDocumentId(_iterator->key()));

        if (_index->hasStoredValues()) {
          auto data = SliceCoveringDataWithStoredValues(
              key,
              RocksDBValue::hashvalueIndexStoredValues(_iterator->value()));
          cb(documentId, data);
        } else {
          auto data = SliceCoveringData(key);
          cb(documentId, data);
        }
      }

      if (!advance()) {
        // validate that Iterator is in a good shape and hasn't failed
        arangodb::rocksutils::checkIteratorStatus(_iterator.get());
        return false;
      }

      --limit;
      if (limit == 0) {
        return true;
      }
    } while (true);
  }

  void skipImpl(uint64_t count, uint64_t& skipped) override {
    ensureIterator();
    TRI_ASSERT(_trx->state()->isRunning());
    TRI_ASSERT(_iterator != nullptr);

    if (_iterator->Valid() && !outOfRange() && count > 0) {
      do {
        TRI_ASSERT(_index->objectId() ==
                   RocksDBKey::objectId(_iterator->key()));

        VPackSlice key =
            RocksDBValue::hashvalueIndexedVPack(_iterator->value());

        if (arangodb::basics::VelocyPackHelper::compare(
                key, _lookupValues.slice(), true, nullptr) == 0) {
          --count;
          ++skipped;
        }

        if (!advance()) {
          break;
        }

        if (count == 0) {
          return;
        }
      } while (true);
    }

    // validate that Iterator is in a good shape and hasn't failed
    arangodb::rocksutils::checkIteratorStatus(_iterator.get());
  }

  /// @brief Reset the cursor
  void resetImpl() override {
    TRI_ASSERT(_trx->state()->isRunning());
    _mustSeek = true;
  }

  /// @brief we provide a method to provide the index attribute values
  /// while scanning the index
  bool hasCovering() const override { return true; }

 private:
  inline bool outOfRange() const {
    // we can effectively disable the out-of-range checks for read-only
    // transactions, as our Iterator is a snapshot-based iterator with a
    // configured iterate_upper_bound/iterate_lower_bound value.
    // this makes RocksDB filter out non-matching keys automatically.
    // however, for a write transaction our Iterator is a rocksdb
    // BaseDeltaIterator, which will merge the values from a snapshot iterator
    // and the changes in the current transaction. here rocksdb will only apply
    // the bounds checks for the base iterator (from the snapshot), but not for
    // the delta iterator (from the current transaction), so we still have to
    // carry out the checks ourselves.

    return _mustCheckBounds &&
           (_cmp->Compare(_iterator->key(), _rangeBound) > 0);
  }

  void ensureIterator() {
    if (_iterator == nullptr) {
      auto state = RocksDBTransactionState::toState(_trx);
      RocksDBTransactionMethods* mthds =
          state->rocksdbMethods(_collection->id());
      _iterator =
          mthds->NewIterator(_index->columnFamily(), [&](ReadOptions& options) {
            // TRI_ASSERT(options.prefix_same_as_start);
            // we need to have a pointer to a slice for the upper bound
            // so we need to assign the slice to an instance variable here
            options.iterate_upper_bound = &_rangeBound;
            options.readOwnWrites = canReadOwnWrites() == ReadOwnWrites::yes;
          });
    }

    TRI_ASSERT(_iterator != nullptr);
    if (_mustSeek) {
      _iterator->Seek(_bounds.start());
      _mustSeek = false;
    }
    TRI_ASSERT(!_mustSeek);
  }

  inline bool advance() {
    _iterator->Next();

    return _iterator->Valid() && !outOfRange();
  }

  arangodb::RocksDBHashvalueIndex const* _index;
  rocksdb::Comparator const* _cmp;
  std::unique_ptr<rocksdb::Iterator> _iterator;
  VPackBuilder _lookupValues;
  uint64_t _hash;
  RocksDBKeyBounds _bounds;
  // used for iterate_upper_bound
  rocksdb::Slice _rangeBound;
  bool _mustSeek;
  bool const _mustCheckBounds;
};

}  // namespace arangodb

uint64_t RocksDBHashvalueIndex::HashForKey(rocksdb::Slice const& key) {
  // NOTE: This function needs to use the same hashing on the
  // indexed VPack as the initial inserter does
  VPackSlice tmp = RocksDBKey::indexedVPack(key);
  return tmp.normalizedHash();
}

/// @brief create the index
RocksDBHashvalueIndex::RocksDBHashvalueIndex(
    IndexId iid, arangodb::LogicalCollection& collection,
    arangodb::velocypack::Slice info)
    : RocksDBIndex(iid, collection, info,
                   RocksDBColumnFamilyManager::get(
                       RocksDBColumnFamilyManager::Family::HashvalueIndex),
                   /*useCache*/ false),
      _estimates(true),
      _estimator(nullptr),
      _storedValues(Index::parseFields(
          info.get(arangodb::StaticStrings::IndexStoredValues),
          /*allowEmpty*/ true, /*allowExpansion*/ false)),
      _coveredFields(Index::mergeFields(fields(), _storedValues)) {
  TRI_ASSERT(_cf == RocksDBColumnFamilyManager::get(
                        RocksDBColumnFamilyManager::Family::HashvalueIndex));

  if (VPackSlice s = info.get(StaticStrings::IndexEstimates); s.isBoolean()) {
    // read "estimates" flag from velocypack if it is present.
    // if it's not present, we go with the default (estimates = true)
    _estimates = s.getBoolean();
  }

  if (_estimates && !ServerState::instance()->isCoordinator() &&
      !collection.isAStub()) {
    // We activate the estimator for all non unique-indexes.
    // And only on single servers and DBServers
    _estimator = std::make_unique<RocksDBCuckooIndexEstimatorType>(
        RocksDBIndex::ESTIMATOR_SIZE);
  }

  TRI_ASSERT(!_fields.empty());
  TRI_ASSERT(iid.isSet());

  fillPaths(_fields, _paths, &_expanding);
  fillPaths(_storedValues, _storedValuesPaths, nullptr);
  TRI_ASSERT(_fields.size() == _paths.size());
  TRI_ASSERT(_storedValues.size() == _storedValuesPaths.size());
}

/// @brief destroy the index
RocksDBHashvalueIndex::~RocksDBHashvalueIndex() = default;

std::vector<std::vector<arangodb::basics::AttributeName>> const&
RocksDBHashvalueIndex::coveredFields() const {
  return _coveredFields;
}

bool RocksDBHashvalueIndex::hasSelectivityEstimate() const {
  return _estimates;
}

double RocksDBHashvalueIndex::selectivityEstimate(std::string_view) const {
  TRI_ASSERT(!ServerState::instance()->isCoordinator());
  if (_estimator == nullptr || !_estimates) {
    // we turn off the estimates for some system collections to avoid updating
    // them too often. we also turn off estimates for stub collections on
    // coordinator and DB servers
    return 0.0;
  }
  TRI_ASSERT(_estimator != nullptr);
  return _estimator->computeEstimate();
}

/// @brief return a VelocyPack representation of the index
void RocksDBHashvalueIndex::toVelocyPack(
    VPackBuilder& builder, std::underlying_type<Serialize>::type flags) const {
  builder.openObject();
  RocksDBIndex::toVelocyPack(builder, flags);

  // serialize storedValues, if they exist
  if (!_storedValues.empty()) {
    builder.add(arangodb::velocypack::Value(
        arangodb::StaticStrings::IndexStoredValues));
    builder.openArray();

    for (auto const& field : _storedValues) {
      std::string fieldString;
      TRI_AttributeNamesToString(field, fieldString);
      builder.add(VPackValue(fieldString));
    }

    builder.close();
  }

  builder.add(StaticStrings::IndexEstimates, VPackValue(_estimates));
  builder.close();
}

/// @brief helper function to insert a document into any index type
/// Should result in an elements vector filled with the new index entries
/// uses the _unique field to determine the kind of key structure
ErrorCode RocksDBHashvalueIndex::fillElement(
    VPackBuilder& leased, LocalDocumentId const& documentId, VPackSlice doc,
    VPackSlice storedValues,
    ::arangodb::containers::SmallVector<IndexValue>& values) {
  if (doc.isNone()) {
    return TRI_ERROR_INTERNAL;
  }

  TRI_ASSERT(leased.isEmpty());
  leased.openArray(true);

  size_t const n = _paths.size();
  for (size_t i = 0; i < n; ++i) {
    TRI_ASSERT(!_paths[i].empty());

    VPackSlice slice = doc.get(_paths[i]);
    if (slice.isNone() || slice.isNull()) {
      // attribute not found
      if (_sparse) {
        // if sparse we do not have to index, this is indicated by result
        // being shorter than n
        return TRI_ERROR_NO_ERROR;
      }
      // null, note that this will be copied later!
      leased.add(VPackSlice::nullSlice());
    } else {
      leased.add(slice);
    }
  }
  leased.close();

  uint64_t hash = leased.slice().normalizedHash();
  RocksDBKey key;
  key.constructHashvalueIndexValue(objectId(), hash, documentId);
  RocksDBValue value =
      RocksDBValue::HashvalueIndexValue(leased.slice(), storedValues);

  values.emplace_back(std::move(key), std::move(value), hash);

  return TRI_ERROR_NO_ERROR;
}

/// @brief helper function to transform AttributeNames into strings.
void RocksDBHashvalueIndex::fillPaths(
    std::vector<std::vector<arangodb::basics::AttributeName>> const& source,
    std::vector<std::vector<std::string>>& paths, std::vector<int>* expanding) {
  paths.clear();
  if (expanding != nullptr) {
    expanding->clear();
  }
  for (std::vector<arangodb::basics::AttributeName> const& list : source) {
    paths.emplace_back();
    std::vector<std::string>& interior(paths.back());
    int expands = -1;
    int count = 0;
    for (auto const& att : list) {
      interior.emplace_back(att.name);
      if (att.shouldExpand) {
        expands = count;
      }
      ++count;
    }
    if (expanding != nullptr) {
      expanding->emplace_back(expands);
    }
  }
}

/// @brief inserts a document into the index
Result RocksDBHashvalueIndex::insert(transaction::Methods& trx,
                                     RocksDBMethods* mthds,
                                     LocalDocumentId const& documentId,
                                     velocypack::Slice doc,
                                     OperationOptions const& options,
                                     bool performChecks) {
  Result res;
  ::arangodb::containers::SmallVector<IndexValue>::allocator_type::arena_type
      valuesArena;
  ::arangodb::containers::SmallVector<IndexValue> values{valuesArena};

  transaction::BuilderLeaser storedValues(&trx);
  if (!_storedValuesPaths.empty()) {
    storedValues->openArray(true);
    for (auto const& it : _storedValuesPaths) {
      VPackSlice s = doc.get(it);
      if (s.isNone()) {
        s = VPackSlice::nullSlice();
      }
      storedValues->add(s);
    }
    storedValues->close();
  }

  {
    // rethrow all types of exceptions from here...
    transaction::BuilderLeaser leased(&trx);
    auto r =
        fillElement(*leased, documentId, doc, storedValues->slice(), values);

    if (r != TRI_ERROR_NO_ERROR) {
      return addErrorMsg(res, r);
    }
  }

  // AQL queries never read from the same collection, after writing into it
  IndexingDisabler guard(
      mthds,
      trx.state()->hasHint(transaction::Hints::Hint::FROM_TOPLEVEL_AQL) &&
          options.canDisableIndexing);

  rocksdb::Status s;
  for (auto const& v : values) {
    TRI_ASSERT(v.key.containsLocalDocumentId(documentId));
    s = mthds->PutUntracked(_cf, v.key, v.value.string());
    if (!s.ok()) {
      res = rocksutils::convertStatus(s, rocksutils::index);
      break;
    }
  }

  if (res.fail()) {
    addErrorMsg(res, doc.get(StaticStrings::KeyString).copyString());
  } else if (_estimates) {
    auto* state = RocksDBTransactionState::toState(&trx);
    auto* trxc = static_cast<RocksDBTransactionCollection*>(
        state->findCollection(_collection.id()));
    TRI_ASSERT(trxc != nullptr);
    for (auto const& v : values) {
      trxc->trackIndexInsert(id(), v.hash);
    }
  }

  return res;
}

/// @brief removes a document from the index
Result RocksDBHashvalueIndex::remove(transaction::Methods& trx,
                                     RocksDBMethods* mthds,
                                     LocalDocumentId const& documentId,
                                     velocypack::Slice doc) {
  TRI_IF_FAILURE("BreakHashIndexRemove") {
    if (type() == arangodb::Index::IndexType::TRI_IDX_TYPE_HASH_INDEX) {
      // intentionally  break index removal
      return Result(TRI_ERROR_INTERNAL,
                    "BreakHashIndexRemove failure point triggered");
    }
  }
  Result res;
  rocksdb::Status s;

  ::arangodb::containers::SmallVector<IndexValue>::allocator_type::arena_type
      valuesArena;
  ::arangodb::containers::SmallVector<IndexValue> values{valuesArena};

  {
    // rethrow all types of exceptions from here...
    transaction::BuilderLeaser leased(&trx);
    auto r =
        fillElement(*leased, documentId, doc, VPackSlice::nullSlice(), values);

    if (r != TRI_ERROR_NO_ERROR) {
      return addErrorMsg(res, r);
    }
  }

  IndexingDisabler guard(
      mthds, !_unique && trx.state()->hasHint(
                             transaction::Hints::Hint::FROM_TOPLEVEL_AQL));

  // non-unique index contain the unique objectID written exactly once
  for (auto const& v : values) {
    s = mthds->SingleDelete(_cf, v.key);

    if (!s.ok()) {
      res.reset(rocksutils::convertStatus(s, rocksutils::index));
    }
  }

  if (res.fail()) {
    TRI_ASSERT(doc.get(StaticStrings::KeyString).isString());
    addErrorMsg(res, doc.get(StaticStrings::KeyString).copyString());
  } else if (_estimates) {
    auto* state = RocksDBTransactionState::toState(&trx);
    auto* trxc = static_cast<RocksDBTransactionCollection*>(
        state->findCollection(_collection.id()));
    TRI_ASSERT(trxc != nullptr);
    for (auto const& v : values) {
      // The estimator is only useful if we are in a non-unique indexes
      TRI_ASSERT(!_unique);
      trxc->trackIndexRemove(id(), v.hash);
    }
  }

  return res;
}

Index::FilterCosts RocksDBHashvalueIndex::supportsFilterCondition(
    std::vector<std::shared_ptr<arangodb::Index>> const& allIndexes,
    arangodb::aql::AstNode const* node,
    arangodb::aql::Variable const* reference, size_t itemsInIndex) const {
  SimpleAttributeEqualityMatcher matcher(this->_fields);
  return matcher.matchAll(this, node, reference, itemsInIndex);
}

/// @brief specializes the condition for use with the index
arangodb::aql::AstNode* RocksDBHashvalueIndex::specializeCondition(
    arangodb::aql::AstNode* node,
    arangodb::aql::Variable const* reference) const {
  SimpleAttributeEqualityMatcher matcher(this->_fields);
  return matcher.specializeOne(this, node, reference);
}

std::unique_ptr<IndexIterator> RocksDBHashvalueIndex::iteratorForCondition(
    transaction::Methods* trx, arangodb::aql::AstNode const* node,
    arangodb::aql::Variable const* reference, IndexIteratorOptions const& opts,
    ReadOwnWrites readOwnWrites, int) {
  TRI_ASSERT(node != nullptr);
  TRI_ASSERT(node->type == aql::NODE_TYPE_OPERATOR_NARY_AND);
  TRI_ASSERT(node->numMembers() >= 1);

  // this will be reused for multiple invocations of getValueAccess
  std::pair<arangodb::aql::Variable const*,
            std::vector<arangodb::basics::AttributeName>>
      paramPair;

  auto getValueAccess = [&](arangodb::aql::AstNode const* comp,
                            arangodb::aql::AstNode const*& access,
                            arangodb::aql::AstNode const*& value) -> bool {
    access = comp->getMember(0);
    value = comp->getMember(1);
    if (!(access->isAttributeAccessForVariable(paramPair) &&
          paramPair.first == reference)) {
      access = comp->getMember(1);
      value = comp->getMember(0);
      if (!(access->isAttributeAccessForVariable(paramPair) &&
            paramPair.first == reference)) {
        // Both side do not have a correct AttributeAccess, this should not
        // happen and indicates
        // an error in the optimizer
        TRI_ASSERT(false);
      }
      return true;
    }
    return false;
  };

  transaction::BuilderLeaser searchValues(trx);
  searchValues->openArray();

  for (auto const& field : _fields) {
    size_t const n = node->numMembers();
    for (size_t i = 0; i < n; ++i) {
      arangodb::aql::AstNode const* comp = node->getMemberUnchecked(i);

      TRI_ASSERT(comp->numMembers() == 2);
      arangodb::aql::AstNode const* access = nullptr;
      arangodb::aql::AstNode const* value = nullptr;
      getValueAccess(comp, access, value);

      if (paramPair.second == field) {
        value->toVelocyPackValue(*searchValues);
      }
    }
  }

  searchValues->close();

  return std::make_unique<RocksDBHashvalueIndexIterator>(
      &_collection, trx, this, searchValues->slice(), readOwnWrites);
}

void RocksDBHashvalueIndex::afterTruncate(TRI_voc_tick_t tick,
                                          arangodb::transaction::Methods* trx) {
  if (unique() || _estimator == nullptr) {
    return;
  }
  TRI_ASSERT(_estimator != nullptr);
  _estimator->bufferTruncate(tick);
  RocksDBIndex::afterTruncate(tick, trx);
}

RocksDBCuckooIndexEstimatorType* RocksDBHashvalueIndex::estimator() {
  return _estimator.get();
}

void RocksDBHashvalueIndex::setEstimator(
    std::unique_ptr<RocksDBCuckooIndexEstimatorType> est) {
  TRI_ASSERT(!_unique);
  TRI_ASSERT(_estimator == nullptr ||
             _estimator->appliedSeq() <= est->appliedSeq());
  _estimator = std::move(est);
}
/*
void RocksDBHashvalueIndex::recalculateEstimates() {
  if (unique() || _estimator == nullptr) {
    return;
  }
  TRI_ASSERT(_estimator != nullptr);
  _estimator->clear();

  auto& selector =
      _collection.vocbase().server().getFeature<EngineSelectorFeature>();
  auto& engine = selector.engine<RocksDBEngine>();
  rocksdb::TransactionDB* db = engine.db();
  rocksdb::SequenceNumber seq = db->GetLatestSequenceNumber();

  auto bounds = getBounds();
  rocksdb::Slice const end = bounds.end();
  rocksdb::ReadOptions options;
  options.iterate_upper_bound = &end;   // safe to use on rocksb::DB directly
  options.prefix_same_as_start = true;  // key-prefix includes edge
  options.verify_checksums = false;
  options.fill_cache = false;
  std::unique_ptr<rocksdb::Iterator> it(db->NewIterator(options, _cf));
  for (it->Seek(bounds.start()); it->Valid(); it->Next()) {
    uint64_t hash = RocksDBHashvalueIndex::HashForKey(it->key());
    // cppcheck-suppress uninitvar ; doesn't understand above call
    _estimator->insert(hash);
  }
  _estimator->setAppliedSeq(seq);
}
*/
