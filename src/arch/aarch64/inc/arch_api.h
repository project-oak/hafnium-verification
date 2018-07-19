#ifndef _ARCH_API_H
#define _ARCH_API_H

/* Keep macro alignment */
/* clang-format off */

/* Return values for vcpu_run() hypervisor call. */
#define HF_VCPU_YIELD              0x00
#define HF_VCPU_WAIT_FOR_INTERRUPT 0x01
#define HF_VCPU_WAKE_UP            0x02

/* TODO: Define constants below according to spec. */
#define HF_VCPU_RUN       0xff00
#define HF_VM_GET_COUNT   0xff01
#define HF_VCPU_GET_COUNT 0xff02

/* clang-format on */

#endif /* _ARCH_API_H */
