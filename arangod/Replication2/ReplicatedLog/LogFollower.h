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
/// @author Tobias Gödderz
////////////////////////////////////////////////////////////////////////////////

#pragma once

#include "Replication2/LoggerContext.h"
#include "Replication2/ReplicatedLog/ILogInterfaces.h"
#include "Replication2/ReplicatedLog/InMemoryLog.h"
#include "Replication2/ReplicatedLog/LogCommon.h"
#include "Replication2/ReplicatedLog/LogCore.h"
#include "Replication2/ReplicatedLog/NetworkMessages.h"
#include "Replication2/ReplicatedLog/ReplicatedLogMetrics.h"
#include "Replication2/ReplicatedLog/WaitForBag.h"
#include "Replication2/ReplicatedLog/types.h"

#include <Basics/Guarded.h>
#include <Futures/Future.h>

#include <condition_variable>
#include <map>
#include <memory>
#include <mutex>

namespace arangodb::replication2::replicated_log {

/**
 * @brief Follower instance of a replicated log.
 */
class LogFollower : public ILogFollower,
                    public std::enable_shared_from_this<LogFollower> {
 public:
  ~LogFollower() override;
  static auto construct(
      LoggerContext const&, std::shared_ptr<ReplicatedLogMetrics> logMetrics,
      std::shared_ptr<ReplicatedLogGlobalSettings const> options,
      ParticipantId id, std::unique_ptr<LogCore> logCore, LogTerm term,
      std::optional<ParticipantId> leaderId) -> std::shared_ptr<LogFollower>;

  // follower only
  [[nodiscard]] auto appendEntries(AppendEntriesRequest)
      -> futures::Future<AppendEntriesResult> override;

  [[nodiscard]] auto getStatus() const -> LogStatus override;
  [[nodiscard]] auto getQuickStatus() const -> QuickLogStatus override;
  [[nodiscard]] auto
  resign() && -> std::tuple<std::unique_ptr<LogCore>, DeferredAction> override;
  [[nodiscard]] auto getLeader() const noexcept
      -> std::optional<ParticipantId> const& override;

  [[nodiscard]] auto waitFor(LogIndex) -> WaitForFuture override;
  [[nodiscard]] auto waitForIterator(LogIndex index)
      -> WaitForIteratorFuture override;
  [[nodiscard]] auto waitForResign() -> futures::Future<futures::Unit> override;
  [[nodiscard]] auto getParticipantId() const noexcept
      -> ParticipantId const& override;
  [[nodiscard]] auto getLogIterator(LogIndex firstIndex) const
      -> std::unique_ptr<LogIterator>;
  [[nodiscard]] auto getCommittedLogIterator(LogIndex firstIndex) const
      -> std::unique_ptr<LogIterator>;
  [[nodiscard]] auto getCommitIndex() const noexcept -> LogIndex override;

  [[nodiscard]] auto copyInMemoryLog() const -> InMemoryLog override;
  [[nodiscard]] auto release(LogIndex doneWithIdx) -> Result override;

  /// @brief Resolved when the leader has committed at least one entry.
  auto waitForLeaderAcked() -> WaitForFuture override;

 private:
  LogFollower(LoggerContext const&,
              std::shared_ptr<ReplicatedLogMetrics> logMetrics,
              std::shared_ptr<ReplicatedLogGlobalSettings const> options,
              ParticipantId id, std::unique_ptr<LogCore> logCore, LogTerm term,
              std::optional<ParticipantId> leaderId, InMemoryLog inMemoryLog);

  struct GuardedFollowerData {
    GuardedFollowerData() = delete;
    GuardedFollowerData(LogFollower const& self,
                        std::unique_ptr<LogCore> logCore,
                        InMemoryLog inMemoryLog);

    [[nodiscard]] auto getLocalStatistics() const noexcept -> LogStatistics;
    [[nodiscard]] auto getCommittedLogIterator(LogIndex firstIndex) const
        -> std::unique_ptr<LogRangeIterator>;
    [[nodiscard]] auto checkCompaction() -> Result;
    auto checkCommitIndex(LogIndex newCommitIndex, LogIndex newLITK,
                          std::unique_ptr<WaitForQueue> outQueue) noexcept
        -> DeferredAction;
    [[nodiscard]] auto didResign() const noexcept -> bool;

    [[nodiscard]] auto waitForResign()
        -> std::pair<futures::Future<futures::Unit>, DeferredAction>;

    LogFollower const& _follower;
    InMemoryLog _inMemoryLog;
    std::unique_ptr<LogCore> _logCore;
    LogIndex _commitIndex{0};
    LogIndex _lowestIndexToKeep;
    LogIndex _releaseIndex;
    MessageId _lastRecvMessageId{0};
    Guarded<WaitForQueue, arangodb::basics::UnshackledMutex> _waitForQueue;
    WaitForBag _waitForResignQueue;
  };
  std::shared_ptr<ReplicatedLogMetrics> const _logMetrics;
  std::shared_ptr<ReplicatedLogGlobalSettings const> const _options;
  LoggerContext const _loggerContext;
  ParticipantId const _participantId;
  std::optional<ParticipantId> const _leaderId;
  LogTerm const _currentTerm;

  // We use the unshackled mutex because guards are captured by futures.
  // When using a std::mutex we would have to release the mutex in the same
  // thread. Using the UnshackledMutex this is no longer required.
  Guarded<GuardedFollowerData, arangodb::basics::UnshackledMutex>
      _guardedFollowerData;
  std::atomic<bool> _appendEntriesInFlight{false};
  std::condition_variable_any _appendEntriesInFlightCondVar{};

  [[nodiscard]] auto appendEntriesPreFlightChecks(
      GuardedFollowerData const&, AppendEntriesRequest const&) const noexcept
      -> std::optional<AppendEntriesResult>;
};

}  // namespace arangodb::replication2::replicated_log
