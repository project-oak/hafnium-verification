#include <stdio.h>
#include <stdlib.h>

struct Node {
  int value;
  struct Node* next;
//  int x;
};

//@Post: Owned, Unstable { value, next }
struct Node* mpool_alloc();

//@Pre: Owned, { next = NULL } || Unstable { next }
//@Post: n = NULL
struct Node* mpool_free(Node* n);

//@Pre: None
//@Post: Owned
struct Node* create(){
  struct Node* n = mpool_alloc(); //@n: Owned, Unstable { value, next }
  n->value = 0; //@n: Owned, Unstable { next }
  n->next = NULL; //@n: Owned
  return n; //@n: Owned
}

//@Pre: l: Owned
//@Post: Owned
struct Node* prepend(struct Node* l, int val){
  struct Node* n = create(); //@n: Owned, l: Owned
  n->value = val; //@n: Owned, l: Owned
  // relations)
  n->next = l; //@n: Owned, l: Invalid
  return n; //@n: Owned, l: Invalid
}

//@Pre: l: Mutable, *l: Mutable | null
//@Post: l: Mutable, *l: Mutable
void append(struct Node** l, int val){
  struct Node* n = create(); //@n: Owned, l: Mutable, *l: Mutable | null
  struct Node** entry = l; //@n: Owned, entry: Mutable, *entry: Mutable | null, l: Lended

  n->value = val; //@n: Owned, entry: Mutable, *entry: Mutable | null, l: Lended

  while(*entry != NULL){ 
    //@n: Owned, entry: Mutable, *entry: Mutable, l: Lended
    struct Node* elem = *entry; //@n: Owned, elem: Mutable, entry: Lended, *entry: Lended, l: Lended 
    entry = &(elem->next); //@n: Owned, &elem->next: Lended, entry: Mutable
  } //elem is removed. //@entry: Mutable, n: Owned

  //@entry: Mutable, *entry: null, n: Owned, l: Lended
  *entry = n; //@entry: Mutable, n: Invalid
} //

//@Pre: n: Mutable
void delete_next(struct Node* n){
  struct Node* tmp = n->next; //@tmp: Owned, n: Mutable, Unstable { next }, n->next: Invalid
  n->next = tmp->next; //@tmp: Owned, Unstable { next }, n: Mutable 
  mpool_free(tmp); //Use the pre-condition of mpool_free: tmp: NULL, n: Mutable
}

//@Pre: l: Mutable
//
void remove_elem(struct Node** l, int val){
  struct Node* prev //@prev: Invalid, l: Mutable
  struct Node* cur; //@prev: Invalid, cur: Invalid, l: Mutable
  if(*l == NULL)
    return;

  if((*l)->value == val){
    mpool_free(*l); //l: Mutable, Unstable { *l }
    *l = NULL; //l: Mutable
    return;
  }

  prev = *l; //@prev: Mutable, *l: Lended
  cur = prev->next; //@cur: Mutable || NULL, prev: Mutable, prev->next: Lended, *l: Lended

  while(cur != NULL){
    if(cur->value == val){
      delete_next(prev); //@cur: Mutable, prev: Mutable - at this point, cur becomes invalid and prev recovers its right to access the location.
      break;
    }
    prev = cur; //@cur: Lended, prev: Mutable
    cur = prev->next; //@cur: Mutable, prev: Lended, prev->next: Lended
  }
}
