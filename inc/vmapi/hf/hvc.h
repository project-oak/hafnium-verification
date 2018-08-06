#ifndef _VMAPI_HF_HVC_H
#define _VMAPI_HF_HVC_H

/* Keep macro alignment */
/* clang-format off */

/* Return values for vcpu_run() hypervisor call. */
#define HF_VCPU_YIELD              0x00
#define HF_VCPU_WAIT_FOR_INTERRUPT 0x01
#define HF_VCPU_WAKE_UP            0x02
#define HF_VCPU_RESPONSE_READY     0x03

/* TODO: Define constants below according to spec. */
#define HF_VCPU_RUN         0xff00
#define HF_VM_GET_COUNT     0xff01
#define HF_VCPU_GET_COUNT   0xff02
#define HF_VM_CONFIGURE     0xff03
#define HF_RPC_REQUEST      0xff04
#define HF_RPC_READ_REQUEST 0xff05
#define HF_RPC_ACK          0xff06
#define HF_RPC_REPLY        0xff07

/* clang-format on */

#endif /* _VMAPI_HF_HVC_H */
