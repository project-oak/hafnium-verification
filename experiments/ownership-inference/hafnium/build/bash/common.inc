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

# Fail on any error.
set -e
# Fail on any part of a pipeline failing.
set -o pipefail
# Treat unset variables as an error.
set -u
# Display commands being run.
set -x

# Returns absolute path to a file or a directory. The path must exist.
function abs_path() {
	local rel_path="$1"
	if [ -d "$rel_path" ]
	then
		# Parameter is a directory
		local rel_dir="$rel_path"
		local rel_base=""
	elif [ -f "$rel_path" ]
	then
		# Parameter is a regular file
		local rel_dir="$(dirname "$rel_path")"
		local rel_base="/$(basename "$rel_path")"
	else
		# File does not exist
		echo "File not found: $rel_path" >&2
		exit 1
	fi
	echo "$(cd $rel_dir && pwd)$rel_base"
	return 0
}

# Returns true if the environment contains Kokoro build variables.
function is_kokoro_build() {
	[ -v KOKORO_JOB_NAME ]
	return $?
}

# Returns true if the `.repo_manifest` folder exists. The folder should contain
# the manifest and be present in all Repo builds. Eventually this should be
# obsolete as we switch exclusively to Repo.
function is_repo_build() {
	[ -d "${ROOT_DIR}/.repo_manifest" ]
	return $?
}

# Returns absolute path to the source file that called this function.
function get_script_path() {
	abs_path "${BASH_SOURCE[1]}"
}

# Returns absolute path to the directory containing the source file that called
# this function.
function get_script_dir() {
	local caller_path="${BASH_SOURCE[1]}"
	local caller_abs_path="$(abs_path $caller_path)"
	dirname "$caller_abs_path"
}

# Assigns value (second arg) of a variable (first arg) if it is not set already.
function default_value {
	local var_name=$1
	local value=$2
	export ${var_name}=${!var_name:-${value}}
}

# Returns true if `git status` reports uncommitted changes in the source tree.
# Runs on all projects if Repo is detected.
function is_repo_dirty() {
	local cmd=(git status --porcelain=v1)
	if is_repo_build
	then
		# This source tree was checked out using `repo`. Check the
		# status of all projects.
		cmd=(${REPO} forall -c "${cmd[@]}")
	fi
	! (u="$(${cmd[@]})" && test -z "$u")
	return $?
}

# Prepares the source directory for building. This includes setting global
# variables and workaronuds for different build environments.
function init_build() {
	##
	## Find Hafnium's root directory.
	##
	ROOT_DIR="$(abs_path $(get_script_dir)/../..)"
	# Temporary workaround for Repo builds. Check if there is a project
	# folder specific to Repo builds in a parent directory. If it is, the
	# root is further one level up.
	if [ -d "${ROOT_DIR}/../.repo_manifest" ]
	then
		ROOT_DIR="$(dirname ${ROOT_DIR})"
	fi

	##
	## Paths to tools
	##
	CLANG="${ROOT_DIR}/prebuilts/linux-x64/clang/bin/clang"
	REPO="${ROOT_DIR}/prebuilts/generic/repo/repo"

	##
	## Workarounds for Kokoro+Repo builds.
	##
	if is_kokoro_build && is_repo_build
	then
		# Kokoro does not correctly initialize the `.repo` folder which
		# causes `is_repo_dirty` checks to fail. We check out the
		# manifest as one of the projects and use it to initialize the
		# `.repo` folder here.
		(cd "${ROOT_DIR}/.repo_manifest" && git branch master)
		(cd "${ROOT_DIR}" && "${REPO}" init -u .repo_manifest)
		# Kokoro does not support '<linkfile>' manifest tags. Parse the
		# manifest and symlink files here.
		"$(get_script_dir)/symlink_repo.py" "${ROOT_DIR}"
	fi
}
