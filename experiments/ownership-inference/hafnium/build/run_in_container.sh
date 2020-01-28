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
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname ${SCRIPT_DIR})"

source "${SCRIPT_DIR}/docker/common.inc"

if [ "${HAFNIUM_HERMETIC_BUILD:-}" == "inside" ]
then
	echo "ERROR: Invoked $0 recursively" 1>&2
	exit 1
fi

# Set up a temp directory and register a cleanup function on exit.
TMP_DIR="$(mktemp -d)"
function cleanup() {
	rm -rf "${TMP_DIR}"
}
trap cleanup EXIT

# Build local image and write its hash to a temporary file.
IID_FILE="${TMP_DIR}/imgid.txt"
"${DOCKER}" build \
	--build-arg LOCAL_UID="$(id -u)" \
	--build-arg LOCAL_GID="$(id -g)" \
	--iidfile="${IID_FILE}" \
	-f "${SCRIPT_DIR}/docker/Dockerfile.local" \
	"${SCRIPT_DIR}/docker"
IMAGE_ID="$(cat ${IID_FILE})"

# Parse command line arguments
INTERACTIVE=false
ALLOW_PTRACE=false
while true
do
	case "${1:-}" in
	-i)
		INTERACTIVE=true
		shift
		;;
	-p)
		ALLOW_PTRACE=true
		shift
		;;
	-*)
		echo "ERROR: Unknown command line flag: $1" 1>&2
		echo "Usage: $0 [-i] [-p] <command>"
		exit 1
		;;
	*)
		break
		;;
	esac
done

ARGS=()
# Run with a pseduo-TTY for nicer logging.
ARGS+=(-t)
# Run interactive if this script was invoked with '-i'.
if [ "${INTERACTIVE}" == "true" ]
then
	ARGS+=(-i)
fi
# Allow ptrace() syscall if invoked with '-p'.
if [ "${ALLOW_PTRACE}" == "true" ]
then
	echo "WARNING: Docker seccomp profile is disabled!" 1>&2
	ARGS+=(--cap-add=SYS_PTRACE --security-opt seccomp=unconfined)
fi
# Propagate "HAFNIUM_*" environment variables.
# Note: Cannot use `env | while` because the loop would run inside a child
# process and would not have any effect on variables in the parent.
while read -r ENV_LINE
do
	VAR_NAME="$(echo ${ENV_LINE} | cut -d= -f1)"
	case "${VAR_NAME}" in
	HAFNIUM_HERMETIC_BUILD)
		# Skip this one. It will be overridden below.
		;;
	HAFNIUM_*)
		ARGS+=(-e "${ENV_LINE}")
		;;
	esac
done <<< "$(env)"
# Set environment variable informing the build that we are running inside
# a container.
ARGS+=(-e HAFNIUM_HERMETIC_BUILD=inside)
# Bind-mount the Hafnium root directory. We mount it at the same absolute
# location so that all paths match across the host and guest.
ARGS+=(-v "${ROOT_DIR}":"${ROOT_DIR}")
# Make all files outside of the Hafnium directory read-only to ensure that all
# generated files are written there.
ARGS+=(--read-only)
# Mount a writable /tmp folder. Required by LLVM/Clang for intermediate files.
ARGS+=(--tmpfs /tmp)
# Set working directory.
ARGS+=(-w "${ROOT_DIR}")

echo "Running in container: $*" 1>&2
${DOCKER} run \
	${ARGS[@]} \
	"${IMAGE_ID}" \
	/bin/bash -c "$*"
