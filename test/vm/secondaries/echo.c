#include <stdalign.h>
#include <stdint.h>

#include "hf/mm.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

alignas(4096) uint8_t kstack[4096];

static alignas(PAGE_SIZE) uint8_t send_page[PAGE_SIZE];
static alignas(PAGE_SIZE) uint8_t recv_page[PAGE_SIZE];

static hf_ipaddr_t send_page_addr = (hf_ipaddr_t)send_page;
static hf_ipaddr_t recv_page_addr = (hf_ipaddr_t)recv_page;

void kmain(void)
{
	hf_vm_configure(send_page_addr, recv_page_addr);
	hf_vm_configure(send_page_addr, recv_page_addr);

	/* Loop, echo messages back to the sender. */
	for (;;) {
		uint64_t ret = hf_mailbox_receive(true);
		uint32_t vm_id = HF_MAILBOX_RECEIVE_VM_ID(ret);
		uint32_t size = HF_MAILBOX_RECEIVE_SIZE(ret);
		memcpy(send_page, recv_page, size);
		hf_mailbox_clear();
		hf_mailbox_send(vm_id, size);
	}
}
