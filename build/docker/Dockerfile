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
# Base container image to be uploaded to Google Cloud Platform as
# "eu.gcr.io/hafnium-build/hafnium_ci". Each user derives their own container
# with local user permissions from this base image. It should contain everything
# needed to build and test Hafnium.
#
FROM launcher.gcr.io/google/ubuntu1804
MAINTAINER Hafnium Team <hafnium-team+build@google.com>

# Install dependencies. Clear APT cache at the end to save space.
ENV DEBIAN_FRONTEND=noninteractive
RUN 	apt-get update \
	&& apt-get install -y \
		bc                             `# for Linux headers` \
		binutils-aarch64-linux-gnu \
		bison \
		build-essential \
		cpio \
		device-tree-compiler \
		flex \
		git \
		libpixman-1-0                  `# for QEMU` \
		libsdl2-2.0-0                  `# for QEMU` \
		libglib2.0                     `# for QEMU` \
		libssl-dev                     `# for Linux headers` \
		python \
		python-git                     `# for Linux checkpatch` \
		python-ply                     `# for Linux checkpatch` \
	&& rm -rf /var/lib/apt/lists/*
