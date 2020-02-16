/*
<type>

full_type := o_type, stability             (* pair of ownership and stability *)
           | full_type + full_type         (* OR full type: we really need this? *)
o_type    := o_type + o_type               (* OR ownership type *)
           | ownership (full_type)         (* nested ownership type *)
           | ownership c_type ?f_types     (* ownership for C types *)
           | lended (var)                  (* lended reference *)
           | null                          (* null reference *)
           | invalid                       (* invalid reference. we usally omit "invalid", but sometimes it is needed. *)
ownership := *own                          (* owned reference *)
           | *mut                          (* mutable reference *)
           | *shd                          (* shared reference *)
stability := stable                        (* stable. we omit "stable" usually. *)
           | unstable { fields }           (* unstable for the fields *)
f_types   := { (field:o_type)+ }           (* ownership for sub fields *)
 */

#include <stdio.h>
#include <stdlib.h>

struct Node {
  int value; 
  struct Node* next;
};

// Comment by Kang: Unstable {} != Stable (because of relational 
// properties)

//[post] ret: *own Node, unstable { value, next }
struct Node* mpool_alloc();

//[pre]  n: *own Node { next:null } + *own Node, unstable { next }
//[post] n: invalid
struct void mpool_free(Node* n);

//[post] ret: *own Node
struct Node* create(){
  //@
  struct Node* n = mpool_alloc(); 
  //@ n: *own Node, unstable { value, next }
  n->value = 0; //@n: Owned, Unstable { next }
  //@ n: *own Node, unstable { next }
  n->next = NULL; 
  //@ n: Owned
  return n; 
  //@ Bot
}

//[pre] l: *own Node
//[post] ret: *own Node
struct Node* prepend(struct Node* l, int val){
  //@ l: *own Node
  struct Node* n = create(); 
  //@ n: *own Node, l: *own Node
  n->value = val; 
  //@ n: *own Node, l: *own Node
  n->next = l; 
  //@ n: *own Node
  return n; 
  //@ Bot
}

//[pre]  l: *mut (*own Node + null)
//[post] l: *mut (*own Node)
void append(struct Node** l, int val){
  //@ l: *mut (*own Node + null)
  struct Node* n = create(); 
  //@ n: *own Node, l: *mut (*own Node + null)
  struct Node** entry = l;
  //@ n: *own Node, entry: *mut (*mut Node + null), l: lended(entry)

  n->value = val; 
  //@ n: *own Node, entry: *mut (*mut Node + null), l: lended(entry)
  
  // Comment by Kang: we should solve some constraints to discover loop 
  // invariants
  while(*entry != NULL){  
    //@ n: *own Node, entry: *mut (*mut Node), l: lended(entry)
    struct Node* elem = *entry; 
    //@ n: *own Node, elem: *mut Node, entry: *mut (lended(elem)), l: 
    //lended(entry)
   
    // Comment by Kang: At this point, we can choose 1) entry should be 
    // invalidated or 2) entry should be lended but eventually 
    // invalidated next time.
    
    entry = &(elem->next); 
    //@ n: *own Node, elem: *mut Node { next:lended(entry) }, entry: 
    //*mut (*mut Node + null), l: *mut (lended(elem))
    
    // Note that elem goes out of scope at this point. 
    //@ n: *own Node, entry: *mut (*mut Node + null), l: *mut (*mut Node 
    //{ next: lended(entry) })
  } 

  //@ n: *own Node, entry: *mut (*mut Node + null), l: lended(entry)
  *entry = n; 
  //@ entry: *mut (*mut Node), l: lended(entry)
  
  // Note that entry goes out of scope at this point.
  //@ l: *mut (*mut Node) 
} 

//[pre]  n: *mut Node
//[post]  n: *mut Node
void delete_next(struct Node* n){
  //@ n: *mut Node
  struct Node* tmp = n->next; 
  //@ tmp: *own Node, n: *mut Node { next: invalid }, unstable { next }
  n->next = tmp->next; 
  //@ tmp: *own Node { next: invalid }, unstable { next }, n: *mut Node
  mpool_free(tmp); 
  //@ n: *mut Node
}

//[pre] l: *mut (*own Node + null)
void remove_elem(struct Node** l, int val){
  //@ l: *mut (*own Node + null)
  struct Node* prev;
  //@ prev: invalid, l: *mut (*own Node + null)
  struct Node* cur; 
  //@ cur: invalid, prev: invalid, l: *mut (*own Node + null)
  
  if(*l == NULL){
    //@ cur: invalid, prev: invalid, l: *mut (null)
    return;
    //@ Bot
  }

  //@ cur: invalid, prev: invalid, l: *mut (*own Node)
  if((*l)->value == val){
    //@ cur: invalid, prev: invalid, l: *mut (*own Node)
    struct Node* tmp = (*l)->next;
    //@ tmp: *own Node + null, cur: invalid, prev: invalid, l: *mut 
    //(*own Node { next: invalid }, unstable { next })
    mpool_free(*l); 
    //@ tmp: *own Node + null, cur: invalid, prev: invalid, l: *mut 
    //(invalid)
    *l = tmp; 
    //@ tmp: invalid, cur: invalid, prev: invalid, l: *mut (*own Node + 
    //null)
    return;
    //@ Bot
  }
  
  //@ cur: invalid, prev: invalid, l: *mut (*own Node)
  prev = *l; 
  //@ cur: invalid, prev: *mut Node, l: *mut (lended(prev))
  cur = prev->next; 
  //@ cur: *mut Node + null, prev: *mut Node { next:lended(cur) }, l: 
  //*mut (lended(prev))

  while(cur != NULL){
    //@ cur: *mut Node, prev: *mut Node { next:lended(cur) }, l: *mut 
    //(lended(prev))
    if(cur->value == val){
      //@ cur: *mut Node, prev: *mut Node { next:lended(cur) }, l: *mut 
      //(lended(prev))
      
      // Note that at this point, cur should be invalidated and prev 
      // recovers its full ownership.
      //@ cur: invalid, prev: *mut Node, l: *mut (lended(prev))
      delete_next(prev); 
      //@ cur: invalid, prev: *mut Node, l: *mut (lended(prev))      
      return;
      //@ Bot
    }
    //@ cur: *mut Node, prev: *mut Node { next:lended(cur) }, l: *mut 
    //(lended(prev))
    prev = cur; 
    //@ cur: lended(prev), prev: *mut Node, l: *mut (*mut Node { 
    //next:lended(cur) })
    cur = prev->next; 
    //@ cur: *mut Node, prev: *mut Node { next:lended(cur) }, l: *mut 
    //(*mut Node { next:lended(prev) })
  }
}
