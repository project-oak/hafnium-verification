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

#include <array>
#include <cstdio>
#include <span>
#include <sstream>

#include <gmock/gmock.h>

extern "C" {
#include "hf/manifest.h"
}

namespace
{
using ::testing::ElementsAre;
using ::testing::Eq;
using ::testing::IsEmpty;
using ::testing::NotNull;

template <typename T>
void exec(const char *program, const char *args[], const T &stdin,
	  std::vector<char> *stdout)
{
	/* Create two pipes, one for stdin and one for stdout. */
	int pipes[2][2];
	pipe(pipes[0]);
	pipe(pipes[1]);

	/* Assign FDs for reading/writing by the parent/child. */
	int parent_read_fd = pipes[1][0];  /* stdout pipe, read FD */
	int parent_write_fd = pipes[0][1]; /* stdin pipe, write FD */
	int child_read_fd = pipes[0][0];   /* stdin pipe, read FD */
	int child_write_fd = pipes[1][1];  /* stdout pipe, write FD */

	if (fork()) {
		/* Parent process. */
		std::array<char, 128> buf;
		ssize_t res;

		/* Close child FDs which won't be used. */
		close(child_read_fd);
		close(child_write_fd);

		/* Write to stdin. */
		for (size_t count = 0; count < stdin.size();) {
			res = write(parent_write_fd, stdin.data() + count,
				    stdin.size() - count);
			if (res < 0) {
				std::cerr << "IO error" << std::endl;
				exit(1);
			}
			count += res;
		}
		close(parent_write_fd);

		/* Read from stdout. */
		while (true) {
			res = read(parent_read_fd, buf.data(), buf.size());
			if (res == 0) {
				/* EOF */
				break;
			} else if (res < 0) {
				std::cerr << "IO error" << std::endl;
				exit(1);
			}
			stdout->insert(stdout->end(), buf.begin(),
				       buf.begin() + res);
		}
		close(parent_read_fd);
	} else {
		/* Child process. */

		/* Redirect stdin/stdout to read/write FDs. */
		dup2(child_read_fd, STDIN_FILENO);
		dup2(child_write_fd, STDOUT_FILENO);

		/* Close all FDs which are now unused. */
		close(child_read_fd);
		close(child_write_fd);
		close(parent_read_fd);
		close(parent_write_fd);

		/* Execute the given program. */
		execv(program, const_cast<char *const *>(args));
	}
}

/**
 * Class for programatically building a Device Tree.
 *
 * Usage:
 *   std::vector<char> dtb = ManifestDtBuilder()
 *       .Command1()
 *       .Command2()
 *       ...
 *       .CommandN()
 *       .Build();
 */
class ManifestDtBuilder
{
       public:
	ManifestDtBuilder()
	{
		dts_ << "/dts-v1/;" << std::endl;
		dts_ << std::endl;

		/* Start root node. */
		StartChild("/");
	}

	std::vector<char> Build(bool dump = false)
	{
		const char *program = "./build/image/dtc.py";
		const char *dtc_args[] = {program, "compile", NULL};
		std::vector<char> dtc_stdout;

		/* Finish root node. */
		EndChild();

		if (dump) {
			Dump();
		}

		exec(program, dtc_args, dts_.str(), &dtc_stdout);
		return dtc_stdout;
	}

	void Dump()
	{
		std::cerr << dts_.str() << std::endl;
	}

	ManifestDtBuilder &StartChild(const std::string_view &name)
	{
		dts_ << name << " {" << std::endl;
		return *this;
	}

	ManifestDtBuilder &EndChild()
	{
		dts_ << "};" << std::endl;
		return *this;
	}

	ManifestDtBuilder &Compatible(const std::vector<std::string_view>
					      &value = {"hafnium,hafnium"})
	{
		return StringListProperty("compatible", value);
	}

	ManifestDtBuilder &DebugName(const std::string_view &value)
	{
		return StringProperty("debug_name", value);
	}

	ManifestDtBuilder &KernelFilename(const std::string_view &value)
	{
		return StringProperty("kernel_filename", value);
	}

	ManifestDtBuilder &RamdiskFilename(const std::string_view &value)
	{
		return StringProperty("ramdisk_filename", value);
	}

	ManifestDtBuilder &VcpuCount(uint32_t value)
	{
		return IntegerProperty("vcpu_count", value);
	}

	ManifestDtBuilder &MemSize(uint32_t value)
	{
		return IntegerProperty("mem_size", value);
	}

	ManifestDtBuilder &SmcWhitelist(const std::vector<uint32_t> &value)
	{
		return IntegerListProperty("smc_whitelist", value);
	}

	ManifestDtBuilder &SmcWhitelistPermissive()
	{
		return BooleanProperty("smc_whitelist_permissive");
	}

	ManifestDtBuilder &Property(const std::string_view &name,
				    const std::string_view &value)
	{
		dts_ << name << " = " << value << ";" << std::endl;
		return *this;
	}

       private:
	ManifestDtBuilder &StringProperty(const std::string_view &name,
					  const std::string_view &value)
	{
		dts_ << name << " = \"" << value << "\";" << std::endl;
		return *this;
	}

	ManifestDtBuilder &StringListProperty(
		const std::string_view &name,
		const std::vector<std::string_view> &value)
	{
		bool is_first = true;

		dts_ << name << " = ";
		for (const std::string_view &entry : value) {
			if (is_first) {
				is_first = false;
			} else {
				dts_ << ", ";
			}
			dts_ << "\"" << entry << "\"";
		}
		dts_ << ";" << std::endl;
		return *this;
	}

	ManifestDtBuilder &IntegerProperty(const std::string_view &name,
					   uint32_t value)
	{
		dts_ << name << " = <" << value << ">;" << std::endl;
		return *this;
	}

	ManifestDtBuilder &IntegerListProperty(
		const std::string_view &name,
		const std::vector<uint32_t> &value)
	{
		dts_ << name << " = < ";
		for (const uint32_t entry : value) {
			dts_ << entry << " ";
		}
		dts_ << ">;" << std::endl;
		return *this;
	}

	ManifestDtBuilder &BooleanProperty(const std::string_view &name)
	{
		dts_ << name << ";" << std::endl;
		return *this;
	}

	std::stringstream dts_;
};

static bool get_fdt_root(const std::vector<char> &dtb,
			 struct fdt_node *fdt_root)
{
	const struct fdt_header *fdt_header;

	fdt_header = reinterpret_cast<const struct fdt_header *>(dtb.data());
	return fdt_root_node(fdt_root, fdt_header) &&
	       fdt_find_child(fdt_root, "");
}

TEST(manifest, no_hypervisor_node)
{
	struct manifest m;
	struct fdt_node fdt_root;
	std::vector<char> dtb = ManifestDtBuilder().Build();

	ASSERT_TRUE(get_fdt_root(dtb, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root),
		  MANIFEST_ERROR_NO_HYPERVISOR_FDT_NODE);
}

TEST(manifest, no_compatible_property)
{
	struct manifest m;
	struct fdt_node fdt_root;

	/* clang-format off */
	std::vector<char> dtb = ManifestDtBuilder()
		.StartChild("hypervisor")
		.EndChild()
		.Build();
	/* clang-format on */

	ASSERT_TRUE(get_fdt_root(dtb, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root),
		  MANIFEST_ERROR_PROPERTY_NOT_FOUND);
}

TEST(manifest, not_compatible)
{
	struct manifest m;
	struct fdt_node fdt_root;

	/* clang-format off */
	std::vector<char> dtb = ManifestDtBuilder()
		.StartChild("hypervisor")
			.Compatible({ "foo,bar" })
		.EndChild()
		.Build();
	/* clang-format on */

	ASSERT_TRUE(get_fdt_root(dtb, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root), MANIFEST_ERROR_NOT_COMPATIBLE);
}

TEST(manifest, compatible_one_of_many)
{
	struct manifest m;
	struct fdt_node fdt_root;

	/* clang-format off */
	std::vector<char> dtb = ManifestDtBuilder()
		.StartChild("hypervisor")
			.Compatible({ "foo,bar", "hafnium,hafnium" })
			.StartChild("vm1")
				.DebugName("primary")
			.EndChild()
		.EndChild()
		.Build();
	/* clang-format on */

	ASSERT_TRUE(get_fdt_root(dtb, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root), MANIFEST_SUCCESS);
}

TEST(manifest, no_vm_nodes)
{
	struct manifest m;
	struct fdt_node fdt_root;

	/* clang-format off */
	std::vector<char> dtb = ManifestDtBuilder()
		.StartChild("hypervisor")
			.Compatible()
		.EndChild()
		.Build();
	/* clang-format on */

	ASSERT_TRUE(get_fdt_root(dtb, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root), MANIFEST_ERROR_NO_PRIMARY_VM);
}

static std::vector<char> gen_long_string_dtb(bool valid)
{
	const char last_valid[] = "1234567890123456789012345678901";
	const char first_invalid[] = "12345678901234567890123456789012";
	static_assert(sizeof(last_valid) == STRING_MAX_SIZE);
	static_assert(sizeof(first_invalid) == STRING_MAX_SIZE + 1);

	/* clang-format off */
	return ManifestDtBuilder()
		.StartChild("hypervisor")
			.Compatible()
			.StartChild("vm1")
				.DebugName(valid ? last_valid : first_invalid)
			.EndChild()
		.EndChild()
		.Build();
	/* clang-format on */
}

TEST(manifest, long_string)
{
	struct manifest m;
	struct fdt_node fdt_root;

	std::vector<char> dtb_last_valid = gen_long_string_dtb(true);
	std::vector<char> dtb_first_invalid = gen_long_string_dtb(false);

	ASSERT_TRUE(get_fdt_root(dtb_last_valid, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root), MANIFEST_SUCCESS);

	ASSERT_TRUE(get_fdt_root(dtb_first_invalid, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root), MANIFEST_ERROR_STRING_TOO_LONG);
}

TEST(manifest, reserved_vm_id)
{
	struct manifest m;
	struct fdt_node fdt_root;

	/* clang-format off */
	std::vector<char> dtb = ManifestDtBuilder()
		.StartChild("hypervisor")
			.Compatible()
			.StartChild("vm1")
				.DebugName("primary_vm")
			.EndChild()
			.StartChild("vm0")
				.DebugName("reserved_vm")
				.VcpuCount(1)
				.MemSize(0x1000)
				.KernelFilename("kernel")
			.EndChild()
		.EndChild()
		.Build();
	/* clang-format on */

	ASSERT_TRUE(get_fdt_root(dtb, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root), MANIFEST_ERROR_RESERVED_VM_ID);
}

static std::vector<char> gen_vcpu_count_limit_dtb(uint32_t vcpu_count)
{
	/* clang-format off */
	return ManifestDtBuilder()
		.StartChild("hypervisor")
			.Compatible()
			.StartChild("vm1")
				.DebugName("primary_vm")
			.EndChild()
			.StartChild("vm2")
				.DebugName("secondary_vm")
				.VcpuCount(vcpu_count)
				.MemSize(0x1000)
				.KernelFilename("kernel")
			.EndChild()
		.EndChild()
		.Build();
	/* clang-format on */
}

TEST(manifest, vcpu_count_limit)
{
	struct manifest m;
	struct fdt_node fdt_root;
	std::vector<char> dtb_last_valid = gen_vcpu_count_limit_dtb(UINT16_MAX);
	std::vector<char> dtb_first_invalid =
		gen_vcpu_count_limit_dtb(UINT16_MAX + 1);

	ASSERT_TRUE(get_fdt_root(dtb_last_valid, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root), MANIFEST_SUCCESS);
	ASSERT_EQ(m.vm_count, 2);
	ASSERT_EQ(m.vm[1].secondary.vcpu_count, UINT16_MAX);

	ASSERT_TRUE(get_fdt_root(dtb_first_invalid, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root),
		  MANIFEST_ERROR_INTEGER_OVERFLOW);
}

TEST(manifest, no_ramdisk_primary)
{
	struct manifest m;
	struct fdt_node fdt_root;

	/* clang-format off */
	std::vector<char> dtb = ManifestDtBuilder()
		.StartChild("hypervisor")
			.Compatible()
			.StartChild("vm1")
				.DebugName("primary_vm")
			.EndChild()
		.EndChild()
		.Build();
	/* clang-format on */

	ASSERT_TRUE(get_fdt_root(dtb, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root), MANIFEST_SUCCESS);
	ASSERT_EQ(m.vm_count, 1);
	ASSERT_STREQ(string_data(&m.vm[0].debug_name), "primary_vm");
	ASSERT_STREQ(string_data(&m.vm[0].primary.ramdisk_filename), "");
}

static std::vector<char> gen_malformed_boolean_dtb(
	const std::string_view &value)
{
	/* clang-format off */
	return  ManifestDtBuilder()
		.StartChild("hypervisor")
			.Compatible()
			.StartChild("vm1")
				.DebugName("primary_vm")
				.Property("smc_whitelist_permissive", value)
			.EndChild()
		.EndChild()
		.Build();
	/* clang-format on */
}

TEST(manifest, malformed_booleans)
{
	struct manifest m;
	struct fdt_node fdt_root;

	std::vector<char> dtb_false = gen_malformed_boolean_dtb("\"false\"");
	std::vector<char> dtb_true = gen_malformed_boolean_dtb("\"true\"");
	std::vector<char> dtb_0 = gen_malformed_boolean_dtb("\"<0>\"");
	std::vector<char> dtb_1 = gen_malformed_boolean_dtb("\"<1>\"");

	ASSERT_TRUE(get_fdt_root(dtb_false, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root),
		  MANIFEST_ERROR_MALFORMED_BOOLEAN);

	ASSERT_TRUE(get_fdt_root(dtb_true, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root),
		  MANIFEST_ERROR_MALFORMED_BOOLEAN);

	ASSERT_TRUE(get_fdt_root(dtb_0, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root),
		  MANIFEST_ERROR_MALFORMED_BOOLEAN);

	ASSERT_TRUE(get_fdt_root(dtb_1, &fdt_root));
	ASSERT_EQ(manifest_init(&m, &fdt_root),
		  MANIFEST_ERROR_MALFORMED_BOOLEAN);
}

TEST(manifest, valid)
{
	struct manifest m;
	struct manifest_vm *vm;
	struct fdt_node fdt_root;

	/* clang-format off */
	std::vector<char> dtb = ManifestDtBuilder()
		.StartChild("hypervisor")
			.Compatible()
			.StartChild("vm1")
				.DebugName("primary_vm")
				.KernelFilename("primary_kernel")
				.RamdiskFilename("primary_ramdisk")
				.SmcWhitelist({0x32000000, 0x33001111})
			.EndChild()
			.StartChild("vm3")
				.DebugName("second_secondary_vm")
				.VcpuCount(43)
				.MemSize(0x12345)
				.KernelFilename("second_secondary_kernel")
			.EndChild()
			.StartChild("vm2")
				.DebugName("first_secondary_vm")
				.VcpuCount(42)
				.MemSize(12345)
				.SmcWhitelist({0x04000000, 0x30002222, 0x31445566})
				.SmcWhitelistPermissive()
			.EndChild()
		.EndChild()
		.Build();
	/* clang-format on */

	ASSERT_TRUE(get_fdt_root(dtb, &fdt_root));

	ASSERT_EQ(manifest_init(&m, &fdt_root), MANIFEST_SUCCESS);
	ASSERT_EQ(m.vm_count, 3);

	vm = &m.vm[0];
	ASSERT_STREQ(string_data(&vm->debug_name), "primary_vm");
	ASSERT_STREQ(string_data(&vm->kernel_filename), "primary_kernel");
	ASSERT_STREQ(string_data(&vm->primary.ramdisk_filename),
		     "primary_ramdisk");
	ASSERT_THAT(
		std::span(vm->smc_whitelist.smcs, vm->smc_whitelist.smc_count),
		ElementsAre(0x32000000, 0x33001111));
	ASSERT_FALSE(vm->smc_whitelist.permissive);

	vm = &m.vm[1];
	ASSERT_STREQ(string_data(&vm->debug_name), "first_secondary_vm");
	ASSERT_STREQ(string_data(&vm->kernel_filename), "");
	ASSERT_EQ(vm->secondary.vcpu_count, 42);
	ASSERT_EQ(vm->secondary.mem_size, 12345);
	ASSERT_THAT(
		std::span(vm->smc_whitelist.smcs, vm->smc_whitelist.smc_count),
		ElementsAre(0x04000000, 0x30002222, 0x31445566));
	ASSERT_TRUE(vm->smc_whitelist.permissive);

	vm = &m.vm[2];
	ASSERT_STREQ(string_data(&vm->debug_name), "second_secondary_vm");
	ASSERT_STREQ(string_data(&vm->kernel_filename),
		     "second_secondary_kernel");
	ASSERT_EQ(vm->secondary.vcpu_count, 43);
	ASSERT_EQ(vm->secondary.mem_size, 0x12345);
	ASSERT_THAT(
		std::span(vm->smc_whitelist.smcs, vm->smc_whitelist.smc_count),
		IsEmpty());
	ASSERT_FALSE(vm->smc_whitelist.permissive);
}

} /* namespace */
