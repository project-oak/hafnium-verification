(*
 * Copyright 2020 Jieung Kim (jieungkim@google.com)
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
 *)
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     RelDec
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Require Import Coqlib sflib.


(* From HafniumCore *)
Require Import Lang.
Require Import Types.

Import LangNotations.


Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Local Open Scope N_scope.


Set Implicit Arguments.

(* Criteria : I may need to follow the hafnium's structure as much as possible? 
              It doesn't matter in this prototyping, following the structure is much better
              for us to figure out how we can make prototypes and to compare the real C 
              implementations and these prototypes. *)

Module CPU.

  (* #define STACK_SIZE PAGE_SIZE *)

  (* from cpu.c file *)
  Definition STACK_SIZE := PAGE_SIZE.
  
  (*  Here, we ignore alignment. But, can we ignore static global variable as well? Do we need a specific and corresponding 
      handlers for global static variables? 
            
      alignas(PAGE_SIZE) static char callstacks[MAX_CPUS][STACK_SIZE];
   *)

  (* JIEUNG: Ignoring alignment *)

  Definition callstacks : var := "callstacks".

  (* JIEUNG: Can we express static assertion?  *)
  (* JIEUNG: Ignoring alignment *)
  (*
    static_assert((STACK_SIZE % PAGE_SIZE) == 0, "Keep each stack page aligned.");
    static_assert((PAGE_SIZE % STACK_ALIGN) == 0, "Page alignment is too weak for the stack.");

    alignas(PAGE_SIZE) static uint8_t cpu_message_buffer[MAX_CPUS][PAGE_SIZE];
   *)

  (* JIEUNG: This is 2-D array, but we do not specify ranges in here *)
  Definition cpu_message_buffer : var := "cpu_message_buffer".

  (*
    /* TODO: Fix alignment such that `cpu` structs are in different cache lines. */
    struct cpu {
    /** CPU identifier. Doesn't have to be contiguous. */
    cpu_id_t id;

    /** Pointer to bottom of the stack. */
    void *stack_bottom;

    /** See api.c for the partial ordering on locks. */
    struct spinlock lock;

    /** Determines whether the CPU is currently on. */
    bool is_on;
    };  
   *)

  (* CPU structure accessors *)
  Definition cpu_id_ofs := 0.
  (* JIEUNG: We do not define size of this one... Do we need to do that?  *)
  Definition stack_bottom_ofs := 1.
  Definition lock_ofs := 2.
  Definition is_on_ofs := 3.
  
  Definition cpu_struct_size: nat := 4.

  (* static uint32_t cpu_count = 1; *)
  (* JIEUNG: How can we build the environment for static variable - 
     I think I can handle them when I build ModSem. Is that true? *)
  Definition cpu_count : var := "cpu_count".
 

  (*
  /* State of all supported CPUs. The stack of the first one is initialized. */
  (* JIEUNG: How can we define this kind of initialization? *) 
  struct cpu cpus[MAX_CPUS] = { 
        {
                .is_on = 1,
                (* JIEUNG: we need memory address *)
                .stack_bottom = &callstacks[0][STACK_SIZE],
        },
  };      
  *) 

  (* Ignoring alignment? *)
  (* Definition cpus_struct_size := MAX_CPUS. *)

  (* JIEUNG: global variable. Check its correctness *)
  Definition cpus : var := "cpus".
  
  (*
    uint8_t *cpu_get_buffer(struct cpu *c) 
    {   
        size_t cpu_indx = cpu_index(c);

        CHECK(cpu_indx < MAX_CPUS);

        return cpu_message_buffer[cpu_indx];
    }
   *)

  Definition cpu_get_buffer (c : var) (cpu_indx : var) : stmt :=
    cpu_indx #= (Call "cpu_index" [CBR c]) #;
             Return (cpu_message_buffer #@ cpu_indx).

  (*
    uint32_t cpu_get_buffer_size(struct cpu *c) 
    {   
        size_t cpu_indx = cpu_index(c);
    
        CHECK(cpu_indx < MAX_CPUS);

        return sizeof(cpu_message_buffer[cpu_indx]);
    }
   *)
  
  (* JIEUNG: can we assume that we have built-in functions for those auxiliary things (e.g., sizeof) 
  - have to look up CompCert definitions  *)
  (* JIEUNG: Or can we define the following things with GetLen?: In that case, sizeof sometimes have to be interpreted as 
     GetLen, and sometimes have to be interpreted as normal numbers...  *)
  Definition cpu_get_buffer_size (c : var) (cpu_indx cpu_buf cpu_buf_size: var) : stmt :=
    cpu_indx #= (Call "cpu_index" [CBR c]) #;
             cpu_buf #= (cpu_message_buffer #@ cpu_indx) #;
             cpu_buf_size #= (Call "sizeof" [CBR cpu_buf]) #;
             Return cpu_buf_size.

  (*
  Definition cpu_get_buffer_size (c : var) (cpu_indx cpu_buf cpu_buf_size: var) : stmt :=
    cpu_indx #= (Call "cpu_index" [CBV c]) #;
             Return (GetLen (cpu_message_buffer #@ cpu_indx)).
  *)

  (*
    void cpu_module_init(const cpu_id_t *cpu_ids, size_t count)
    {   
        uint32_t i;
        uint32_t j;
        cpu_id_t boot_cpu_id = cpus[0].id;
        bool found_boot_cpu = false;

        cpu_count = count;

        /*
         * Initialize CPUs with the IDs from the configuration passed in. The
         * CPUs after the boot CPU are initialized in reverse order. The boot
         * CPU is initialized when it is found or in place of the last CPU if it
         * is not found.
         */
        j = cpu_count;
        for (i = 0; i < cpu_count; ++i) {
                struct cpu *c;
                cpu_id_t id = cpu_ids[i];

                if (found_boot_cpu || id != boot_cpu_id) {
                        --j;
                        c = &cpus[j];
                        c->stack_bottom = &callstacks[j][STACK_SIZE];
                } else {
                        found_boot_cpu = true;
                        c = &cpus[0];
                        CHECK(c->stack_bottom == &callstacks[0][STACK_SIZE]);
                }

                sl_init(&c->lock);
                c->id = id;
        }

        if (!found_boot_cpu) {
                /* Boot CPU was initialized but with wrong ID. */
                dlog_warning("Boot CPU's ID not found in config.\n");
                cpus[0].id = boot_cpu_id;
        }
    }
   *)


  (* JIEUNG: I need to figure out whether I used #& correctly or not *)
  (* JIEUNG: #& - ampersand is C's ampersand  *)
  (* JIEUNG: do we need to introduce some guarnatee or assume rules for constant arguments? *)
  Definition cpu_module_init (cpu_ids count: var) (i j boot_cpu_id found_boot_cpu cpu_id c
                                                     cpu_count cpu_info boot_cpu stack_bottom_ofs: var) : stmt :=
    boot_cpu #= (cpus #@ 0) #;
             boot_cpu_id #= (boot_cpu #@ cpu_id_ofs) #;
             found_boot_cpu #= #false #;
             cpu_count #= count #;
             
             (* loop *)
             i #= 0 #;
             j #= cpu_count #;
             
             (#while (i <= cpu_count - 1)
               do (cpu_id #= (cpu_ids #@ i) #;
                          (#if (found_boot_cpu)
                            then j #= (j - 1) #;
                                   c #= (cpus #@ j) #;
                                   stack_bottom_ofs #= (callstacks #@ j) #;
                                   (c @ stack_bottom_ofs #:= (#& (stack_bottom_ofs #@ STACK_SIZE))) #;
                                   (*JIEUNG: I moved this one to each branches to keep its index consistent 
                                     with previous j or i or 0.. *)
                                   (* lock initialization *) 
                                   (c @ lock_ofs #:= (Call "Lock.new" [])) #;
                                   (Call "Lock.release" [CBV (c #@ lock_ofs) ; CBV c]) #;
                                   c @ cpu_id_ofs #:= cpu_id #;
                                   (*JIEUNG: I added the following part for correct behavior... but is it actually correct? *)
                                   cpus @ j #:= c
                            else
                              (#if (!(cpu_id == boot_cpu_id)) then
                                  (* copy and pasted for the previous one *)
                                  j #= (j - 1) #;
                                    c #= (cpus #@ j) #;
                                    stack_bottom_ofs #= (callstacks #@ j) #;
                                    (c @ stack_bottom_ofs #:= (#& (stack_bottom_ofs #@ STACK_SIZE))) #;
                                    (*JIEUNG: I added the following part for correct behavior... but is it actually correct? *)
                                    (*JIEUNG: I moved this one to each branches to keep its index consistent 
                                      with previous j or i or 0.. *)
                                    (* lock initialization *) 
                                    (c @ lock_ofs #:= (Call "Lock.new" [])) #;
                                    (Call "Lock.release" [CBV (c #@ lock_ofs) ; CBV c]) #;
                                    c @ cpu_id_ofs #:= cpu_id #;
                                    (*JIEUNG: I added the following part for correct behavior... but is it actually correct? *)
                                    cpus @ j #:= c
                                else
                                  found_boot_cpu #= #true #;
                                                 c #= (cpus #@ 0) #;
                                                 (*JIEUNG: I added the following part for correct behavior... 
                                                   but is it actually correct? *)
                                                 (*JIEUNG: I moved this one to each branches to keep its index consistent 
                                                   with previous j or i or 0.. *)
                                                 (* lock initialization *) 
                                                 (c @ lock_ofs #:= (Call "Lock.new" [])) #;
                                                 (Call "Lock.release" [CBV (c #@ lock_ofs) ; CBV c]) #;
                                                 c @ cpu_id_ofs #:= cpu_id #;
                                                 (*JIEUNG: I added the following part for correct behavior... 
                                                   but is it actually correct? *)
                                                 cpus @ 0 #:= c)
                                
                          ) #;
                          (* index increasing *) 
                          i #= (i + 1))) #;
             (#if !(found_boot_cpu)
               then (* warning message is ignored *)
                 cpu_info #= (cpus #@ 0) #;
                          cpu_info @ cpu_id_ofs #:= boot_cpu_id #;
                          cpus @ 0 #:= cpu_info
               else Skip).   

  (* JIEUNG: definiing this function in this way is possible, but it is actually a problem. 
     We have to think about a pointer arithmatic in here *) 
  (*
  size_t cpu_index(struct cpu *c)
         {
           return c - cpus;
         }
   *)

  (* JIEUNG: This one is not actually correct. cpus and c are pointers *)
  (* Definition cpu_index (c : var) (i ret: var) : stmt :=
    ret #= Minus c cpus #;
        Return ret.
  *)

  (* do translations for the correct definition *)
  Definition cpu_index (c : var) (i c_i: var) : stmt :=
    i #= 0 #;
      (#while (i <= (MAX_CPUS - 1))
        do (
            c_i #= (cpus #@ i) #;
                #if ((c_i #@ cpu_id_ofs) == (c #@ cpu_id_ofs))
                 then Return i
                 else i #= i + 1)) #;
      (* error case *)
      Return i.
      
           


  (*
    bool cpu_on(struct cpu *c, ipaddr_t entry, uintreg_t arg)
    {   
        bool prev;

        sl_lock(&c->lock);
        prev = c->is_on;
        c->is_on = true;
        sl_unlock(&c->lock);

        if (!prev) {
                struct vm *vm = vm_find(HF_PRIMARY_VM_ID);
                struct vcpu *vcpu = vm_get_vcpu(vm, cpu_index(c));
                struct vcpu_locked vcpu_locked;

                vcpu_locked = vcpu_lock(vcpu);
                vcpu_on(vcpu_locked, entry, arg);
                vcpu_unlock(&vcpu_locked);
        }

        return prev;
    }
   *)

  (* JIEUNG : I am assuming that we have vm related functions in some places - so.. I cannot test this one. 
     But, I can simplify this one to test this module *)
  (* JIEUNG: For lock acquire and release, I followed the semantics that YJ made in Mpool examples. *)
  Definition cpu_on (c entry arg : var) (prev vm vcpu vcpu_locked: var) (idx : var) : stmt :=
    c #= (Call "Lock.acquire" [CBV (c #@ lock_ofs)]) #;   
      prev #=  (c #@ is_on_ofs) #;
      (c @ is_on_ofs #:= #true) #;
      (Call "Lock.release" [CBV (c #@ lock_ofs) ; CBV c]) #;
      #if (!prev)
          then
            vm #= (Call "VM.vm_find" [CBV HF_PRIMARY_VM_ID]) #;
               idx #= (Call "cpu_index" [CBR c]) #;
               (* JIEUNG: Is this CBR correct? *)
               vcpu #= (Call "VM.vm_get_vcpu" [CBR vm; CBV idx]) #;
               (* JIEUNG: Need to add vcpu lock event! I need to check vcpu_lock first though *)
               vcpu_locked #= (Call "VM.vcpu_lock" [CBR vcpu]) #;
               (Call "VM.vcpu_on" [CBV vcpu_locked; CBV entry; CBV arg]) #;
               (Call "VM.vcpu_unlock" [CBV vcpu_locked])
          else
            Return prev 
  .
  

  (*
    void cpu_off(struct cpu *c)
    {
        sl_lock(&c->lock);
        c->is_on = false;
        sl_unlock(&c->lock);
    }
   *)

  Definition cpu_off (c : var) : stmt :=
    c #= (Call "Lock.acquire" [CBV (c #@ lock_ofs)]) #;   
      c @ is_on_ofs #:= #false #;
      (Call "Lock.release" [CBV (c #@ lock_ofs) ; CBV c]).
  
  (*
  struct cpu *cpu_find(cpu_id_t id)
  {
        size_t i;

        for (i = 0; i < cpu_count; i++) {
                if (cpus[i].id == id) {
                        return &cpus[i];
                }
        }

        return NULL;
  }
   *)

  (* JIEUNG: why can we directly assing normal natural numbers into variables? *)
  Definition cpu_find (cpu_id : var) (t_cpu t_cpu_id i : var): stmt :=
    i #= 0 #;
      #while (i <= cpu_count - 1)
      do (t_cpu #= (cpus #@ i) #;
                t_cpu_id #= (t_cpu #@ cpu_id_ofs) #;
                (#if (t_cpu_id == cpu_id)
                  then Return (cpus #@ i)
                  else Skip) #;
                i #= i + 1
         ) #; Return Vnull.
         
End CPU.
