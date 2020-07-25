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
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Local Open Scope N_scope.

Set Implicit Arguments.


Module CPUSeq.

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

void cpu_module_init(const cpu_id_t *cpu_ids, size_t count);

size_t cpu_index(struct cpu *c);
bool cpu_on(struct cpu *c, ipaddr_t entry, uintreg_t arg);
void cpu_off(struct cpu *c);
struct cpu *cpu_find(cpu_id_t id);
uint8_t *cpu_get_buffer(struct cpu *c);
uint32_t cpu_get_buffer_size(struct cpu *c);
   *)  


  (*** DELTA: Ignore the following three things at this moment *)
  (*
uint8_t *cpu_get_buffer(struct cpu *c)
{
    size_t cpu_indx = cpu_index(c);

    CHECK(cpu_indx < MAX_CPUS);

    return cpu_message_buffer[cpu_indx];
}
   *)

  (*
uint32_t cpu_get_buffer_size(struct cpu *c)
{
    size_t cpu_indx = cpu_index(c);

    CHECK(cpu_indx < MAX_CPUS);

    return sizeof(cpu_message_buffer[cpu_indx]);
}
   *)

  (* Can the current language handle the following things? *) 
  (*
/* State of all supported CPUs. The stack of the first one is initialized. */
struct cpu cpus[MAX_CPUS] = {
    {
        .is_on = 1,
        .stack_bottom = &callstacks[0][STACK_SIZE],
    },
};
   *)

  
  (*** DELTA: How can we represent global static variable? *) 
  (* static uint32_t cpu_count = 1; *)

 

  (*
  (*** DELTA: Is it safe to use this kind of context? *)   
  Class CPU_ENV :=
    {
      cpus: nat;
    }.

  Context `{cpu_env: CPU_ENV}.
  *)

  (* static uint32_t cpu_count = 1; *)
  Definition cpus : var := "cpus".
  
  
  (*** DELTA: ignoring locks *)   
  Definition cpu_id_ofs := 0.
  Definition stack_bottom := 1.
  Definition is_on := 2.

  Definition cpu_struct_size : N := 3.

  Definition TRUE := Vnat 1.
  Definition FALSE := Vnat 0.
  
  Fixpoint cpu_struct_wf (p: val): bool :=
    match p with
    | Vptr _ p =>
      match p with
      | [] => true
      | [cpu_id ; stack_bot ;ison] =>
        match cpu_id, stack_bot, ison with
        | Vnat cpu_id', Vptr _ stack_bot', Vnat ison' =>
          if orb (N.eq_dec ison' 0) (N.eq_dec ison' 1) then true 
          else false
        | _, _, _ => false
        end
      | _ => false
      end
    | _ => false
    end
  .

  (*** DELTA: ignoring locks *) 
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

  (*** DELTA: There are some parts that are not precise in the following part. e.g. [cpus] structure - we ignored its definition in this file, but we assume the structure exists *)

  (* Do we need to distiinguish . and -> opeartor in C? *)
  (* it should be ok for autogeneration, but it may require some rewritings when we want to transform loops *)
  
  Definition cpu_module_init (cpus cpu_ids count : var) (boot_cpu_id found_boot_cpu cpu_info cpu_count c id i j : var) : stmt :=
    boot_cpu_id #= (#& (cpus #@ 0)) #;
                found_boot_cpu #= FALSE #;
                cpu_count #= count #;
                j #= cpu_count #;
                (* starting loops *)
                i #= Vnat 0 #;
                #while (Neg (Equal i cpu_count))
                do (
                  id #= (cpu_ids #@ i) #;
                     (#if (found_boot_cpu)
                       then (#if (Neg (Equal id boot_cpu_id))
                              then
                                j #= Minus j (Vnat 1) #;
                                  c #= (#& (cpus #@ j))
                                  (* ignoring stack-bottom thing *)
                                  (* c->stack_bottom = &callstacks[j][STACK_SIZE]; *)
                              else
                                (* How can we distinguish this address assingment and value copy? We have to distinguish 
                                             the case when the value is copied and when we made aliasing by using address copying. 
                                             Do we have some kind of data bases for this kind of things? *) 
                                (found_boot_cpu #= FALSE #;
                                                c #= (cpus #@ 0)))
                       else (found_boot_cpu #= FALSE #;
                                            c #= (cpus #@ 0))) #;
                              (* ignoring lock init *)
                     c @ cpu_id_ofs #:= id #;
                     i #= Plus i (Vnat 1)
                ) #;
                (* the last *)
                #if (Neg found_boot_cpu)
                 then
                   (* can we make the following thing simpler than this *)
                   cpu_info #= (#& (cpus #@ 0)) #;
                            cpu_info @ cpu_id_ofs #:= boot_cpu_id #;
                            cpus @ 0 #:= cpu_info
                 else Skip
  .
    
  (*
size_t cpu_index(struct cpu *c)
{
    return c - cpus;
}
   *)

  Definition cpu_index (c : var) (ret: var) : stmt :=
    ret #= Minus cpus (c #@ cpu_id_ofs) #;
        Return ret.
    
    (*
/**
 * Turns CPU on and returns the previous state.
 */
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

  (*** DELTA: Simplfiication that includes ignoring locks *)
  Definition cpu_on (c entry arg : var) (vm prev idx vcpu: var) : stmt :=
    prev #=  (#& (c #@ is_on)) #;
         #if (prev == Vnat 0)
          then
            (* ignoring its arguments *) 
            vm #= (Call "vm_find" []) #;
               idx #= (Call "cpu_index" [CBV c]) #;
               vcpu #= (Call "vm_get_vcpu" [CBR vm; CBV idx]) #;
               (* need to add lock with vcpu *)
               (Call "vcpu_on" [CBR entry; CBV arg])
          else
            Return prev 
  .
  

  (*
/**
 * Prepares the CPU for turning itself off.
 */
void cpu_off(struct cpu *c)
{
    sl_lock(&c->lock);
    c->is_on = false;
    sl_unlock(&c->lock);
}
   *)

  (*** DELTA: ignoring locks *) 
  
  Definition cpu_off (c : var) : stmt :=
    c @ is_on #:= FALSE.  
    
    (*** DELTA: ignoring the following one with simplification *) 
   
    (* this is a function to find CPUs in the system?  *)
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



  (* Make function signature using body that we have defined - 
    The following things are examples in MPoolSeq 
  Definition initF: function. mk_function_tac init ["p"] ([]: list var). Defined.
  Definition init_with_fallbackF: function.
    mk_function_tac init_with_fallback ["p" ; "fb"] ([]: list var). Defined.
  Definition alloc_contiguousF: function.
    mk_function_tac alloc_contiguous ["p" ; "count"] ["ret"]. Defined.
  Definition alloc_contiguous_no_fallbackF: function.
    mk_function_tac alloc_contiguous_no_fallback
                    ["p" ; "count"] ["prev" ; "ret" ; "new_chunk" ; "chunk"]. Defined.
  Definition alloc_contiguous2F: function.
    mk_function_tac alloc_contiguous2 ["p" ; "count"] ["ret" ; "next" ; "nextp"]. Defined.
  Definition alloc_contiguous_no_fallback2F: function.
    mk_function_tac alloc_contiguous_no_fallback2
                    ["cur" ; "count"] ["ret" ; "next" ; "cur_ofs" ; "new_cur" ]. Defined.
  Definition add_chunkF: function.
    mk_function_tac add_chunk ["p" ; "begin" ; "size"] ["chunk"]. Defined.
  *)

  Definition cpu_offF: function. mk_function_tac cpu_off ["p"] ([]: list var). Defined.

  
End CPUSeq.


Module CPUTEST.

  Include CPUSeq.
  
  Definition main
             (p0: var): stmt :=
    (Put "CPU_PROGRAM Test" Vnull) #;
           p0 #= Vptr None [0: val ; 0: val; Vtrue: val] #;
(*           (Syscall "md" "test:" p0) #; *)
           (Call "cpu_off" [CBR p0]) #;
           (Put "CPU_PROGRAM Tested" Vnull)
  .
          
    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p0"]. Defined.

    Definition program: program :=
      [
        ("main", mainF);
      ("cpu_off", cpu_offF)
      ].

End CPUTEST.
