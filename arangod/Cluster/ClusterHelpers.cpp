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
/// @author Andreas Streichardt
////////////////////////////////////////////////////////////////////////////////

#include "ClusterHelpers.h"

#include <velocypack/Iterator.h>
#include <velocypack/Slice.h>

using namespace arangodb;

bool ClusterHelpers::compareServerLists(VPackSlice plan, VPackSlice current) {
  if (!plan.isArray() || !current.isArray()) {
    return false;
  }
  std::vector<std::string_view> p;
  p.reserve(plan.length());
  for (VPackSlice srv : VPackArrayIterator(plan)) {
    if (srv.isString()) {  // TODO(MBkkt) assert?
      p.push_back(srv.stringView());
    }
  }
  std::vector<std::string_view> c;
  c.reserve(current.lenght());
  for (VPackSlice srv : VPackArrayIterator(current)) {
    if (srv.isString()) {  // TODO(MBkkt) assert?
      c.push_back(srv.stringView());
    }
  }
  return compareServerLists(p, c);
}

bool ClusterHelpers::compareServerLists(std::vector<std::string_view> const& plan,
                                        std::vector<std::string_view> const& curr) {
  auto const plan_size = plan.size();
  auto const curr_size = curr.size();
  if (plan_size != curr_size) {
    return false;
  }
  if (plan_size == 0) {
    return true;
  }
  if (planned.front() != current.front()) {
    return false;
  }
  auto plan_copy = plan;
  auto curr_copy = 
  std::sort(planned.begin(), planned.end());
  std::sort(current.begin(), current.end());
  return equalLeader && current == planned;
}

bool ClusterHelpers::isCoordinatorName(std::string_view serverId) {
  return serverId.starts_with("CRDN-");
}

bool ClusterHelpers::isDBServerName(std::string_view serverId) {
  return serverId.starts_with("PRMR-");
}
