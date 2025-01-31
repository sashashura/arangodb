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
/// @author Andrei Lobov
////////////////////////////////////////////////////////////////////////////////

#include "MaterializeExecutor.h"

#include "Aql/QueryContext.h"
#include "Aql/SingleRowFetcher.h"
#include "Aql/Stats.h"
#include "StorageEngine/PhysicalCollection.h"
#include "StorageEngine/StorageEngine.h"

using namespace arangodb;
using namespace arangodb::aql;

template<typename T>
arangodb::IndexIterator::DocumentCallback
MaterializeExecutor<T>::ReadContext::copyDocumentCallback(ReadContext& ctx) {
  typedef std::function<arangodb::IndexIterator::DocumentCallback(ReadContext&)>
      CallbackFactory;
  static CallbackFactory const callbackFactory{[](ReadContext& ctx) {
    return [&ctx](LocalDocumentId /*id*/, VPackSlice doc) {
      TRI_ASSERT(ctx._outputRow);
      TRI_ASSERT(ctx._inputRow);
      TRI_ASSERT(ctx._inputRow->isInitialized());
      TRI_ASSERT(ctx._infos);
      arangodb::aql::AqlValue a{arangodb::aql::AqlValueHintSliceCopy(doc)};
      bool mustDestroy = true;
      arangodb::aql::AqlValueGuard guard{a, mustDestroy};
      ctx._outputRow->moveValueInto(
          ctx._infos->outputMaterializedDocumentRegId(), *ctx._inputRow, guard);
      return true;
    };
  }};

  return callbackFactory(ctx);
}

template<typename T>
arangodb::aql::MaterializerExecutorInfos<T>::MaterializerExecutorInfos(
    T collectionSource, RegisterId inNmDocId, RegisterId outDocRegId,
    aql::QueryContext& query)
    : _collectionSource(collectionSource),
      _inNonMaterializedDocRegId(inNmDocId),
      _outMaterializedDocumentRegId(outDocRegId),
      _query(query) {}

template<typename T>
arangodb::aql::MaterializeExecutor<T>::MaterializeExecutor(
    MaterializeExecutor<T>::Fetcher& /*fetcher*/, Infos& infos)
    : _trx(infos.query().newTrxContext()),
      _readDocumentContext(infos),
      _infos(infos) {}

template<typename T>
std::tuple<ExecutorState, MaterializeStats, AqlCall>
arangodb::aql::MaterializeExecutor<T>::produceRows(
    AqlItemBlockInputRange& inputRange, OutputAqlItemRow& output) {
  MaterializeStats stats;

  AqlCall upstreamCall{};
  upstreamCall.fullCount = output.getClientCall().fullCount;

  while (inputRange.hasDataRow() && !output.isFull()) {
    bool written = false;

    // FIXME(gnusi): move outside the loop?
    // some micro-optimization
    auto& callback = _readDocumentContext._callback;
    auto docRegId = _readDocumentContext._infos->inputNonMaterializedDocRegId();
    T collectionSource = _readDocumentContext._infos->collectionSource();
    auto const [state, input] =
        inputRange.nextDataRow(AqlItemBlockInputRange::HasDataRow{});

    arangodb::LogicalCollection const* collection = nullptr;
    if constexpr (std::is_same<T, std::string const&>::value) {
      if (_collection == nullptr) {
        _collection = _trx.documentCollection(collectionSource);
      }
      collection = _collection;
    } else {
      collection = reinterpret_cast<arangodb::LogicalCollection const*>(
          input.getValue(collectionSource).slice().getUInt());
    }
    TRI_ASSERT(collection != nullptr);
    _readDocumentContext._inputRow = &input;
    _readDocumentContext._outputRow = &output;

    TRI_IF_FAILURE("MaterializeExecutor::all_fail_and_count") {
      stats.incrFiltered();
      continue;
    }

    TRI_IF_FAILURE("MaterializeExecutor::all_fail") { continue; }

    TRI_IF_FAILURE("MaterializeExecutor::only_one") {
      if (output.numRowsWritten() > 0) {
        continue;
      }
    }

    // FIXME(gnusi): use rocksdb::DB::MultiGet(...)
    written =
        collection->getPhysical()
            ->read(&_trx,
                   LocalDocumentId(input.getValue(docRegId).slice().getUInt()),
                   callback, ReadOwnWrites::no)
            .ok();

    if (written) {
      // document found
      output.advanceRow();
    } else {
      // document not found
      stats.incrFiltered();
    }
  }

  return {inputRange.upstreamState(), stats, upstreamCall};
}

template<typename T>
std::tuple<ExecutorState, MaterializeStats, size_t, AqlCall>
arangodb::aql::MaterializeExecutor<T>::skipRowsRange(
    AqlItemBlockInputRange& inputRange, AqlCall& call) {
  size_t skipped = 0;

  // hasDataRow may only occur during fullCount due to previous overfetching
  TRI_ASSERT(!inputRange.hasDataRow() || call.getOffset() == 0);

  if (call.getOffset() > 0) {
    // we can only account for offset
    skipped += inputRange.skip(call.getOffset());
  } else {
    skipped += inputRange.countAndSkipAllRemainingDataRows();

    skipped += inputRange.skipAll();
  }
  call.didSkip(skipped);

  return {inputRange.upstreamState(), MaterializeStats{}, skipped, call};
}

template class ::arangodb::aql::MaterializeExecutor<RegisterId>;
template class ::arangodb::aql::MaterializeExecutor<std::string const&>;

template class ::arangodb::aql::MaterializerExecutorInfos<RegisterId>;
template class ::arangodb::aql::MaterializerExecutorInfos<std::string const&>;
