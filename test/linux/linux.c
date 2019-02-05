/*
 * Copyright 2019 The Hafnium Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <fcntl.h>
#include <unistd.h>

#include "hf/dlog.h"

#include "hftest.h"
#include <sys/syscall.h>

static int finit_module(int fd, const char *param_values, int flags)
{
	return syscall(SYS_finit_module, fd, param_values, flags);
}

static int delete_module(const char *name, int flags)
{
	return syscall(SYS_delete_module, name, flags);
}

static void insmod_hafnium(void)
{
	int module_file = open("/hafnium.ko", O_RDONLY);
	if (module_file < 0) {
		FAIL("Failed to load Hafnium kernel module from /hafnium.ko");
		return;
	}
	EXPECT_EQ(finit_module(module_file, "", 0), 0);
	close(module_file);
}

static void rmmod_hafnium(void)
{
	EXPECT_EQ(delete_module("hafnium", 0), 0);
}

TEST(linux, load_hafnium)
{
	insmod_hafnium();
	rmmod_hafnium();
}
