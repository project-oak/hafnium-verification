#!/usr/bin/env bash
# Copyright 2019 The Hafnium Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

set -euxo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SCRIPT_PATH="${SCRIPT_DIR}/$(basename "${BASH_SOURCE[0]}")"
ROOT_DIR="$(realpath ${SCRIPT_DIR}/..)"

if [ "${HAFNIUM_HERMETIC_BUILD:-}" == "true" ]
then
	exec "${ROOT_DIR}/build/run_in_container.sh" -p ${SCRIPT_PATH} $@
fi

if [ $# != 1 ]
then
	echo "Usage: $0 <output_file>" 1>&2
	exit 1
fi

MAKE="$(which make)"
STRACE="$(which strace)"

# Set up a temp directory and register a cleanup function on exit.
TMP_DIR="$(mktemp -d)"
function cleanup() {
	rm -rf "${TMP_DIR}"
}
trap cleanup EXIT

STRACE_LOG="${TMP_DIR}/strace.log"

echo "Building with strace"
pushd ${ROOT_DIR}
${MAKE} clobber
${STRACE} \
	-o "${STRACE_LOG}" \
	-f \
	-qq \
	-e trace=%file,chdir,%process \
	${MAKE}
popd

echo "Processing strace output"
"${SCRIPT_DIR}/parse_strace_open.py" ${ROOT_DIR} < "${STRACE_LOG}" > "$1"
