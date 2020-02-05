Module MD0 {
  LS: Type;
  local_state: LS := initial_local_state;

  fun FUN: ? -> ? {
    [** lock **];
    line0;
    [** YIELD **];
    line1;
    [** YIELD **];
    ...
    line40syscall;
    ...
    line70syscall;
    ...
    line100;
    [** unlock **];
  }
}

Module MD1 {
  LS: Type;
  local_state: LS := initial_local_state;
  isRunning: bool := false;
  
  fun FUN: ? -> ? {
    [** lock **];
    assert!(isRunning == false);
    isRunning := true;
    line0;
    [** YIELD **];
    line1;
    [** YIELD **];
    ...
    line40syscall;
    ...
    line70syscall;
    ...
    line100;
    isRunning := false;
    [** unlock **];
  }
}

SimRel: memory는 안건드리고 local state만 건드린다.
local state:
isRunning이 true면 src/tgt 아무거나 허용하고 future relation은 원래거 그대로
isRunning이 false면 src == tgt

Module MD2 {
  LS: Type;
  local_state: LS := initial_local_state;
  isRunning: bool := false;

  fun FUN: ? -> ? {
    [** lock **];
    assert!(isRunning == false);
    isRunning := true;
    [** YIELD **] * 40;
    line0;
    line1;
    ...
    line40syscall;
    [** YIELD **] * 30;
    ...
    line70syscall;
    [** YIELD **] * 30;
    ...
    line100;
    isRunning := false;
    [** unlock **];
  }
}

//연속한 YIELD는 merge 가능하다는 meta-theory

Module MD3 {
  LS: Type;
  local_state: LS := initial_local_state;
  isRunning: bool := false;

  fun FUN: ? -> ? {
    [** lock **];
    assert!(isRunning == false);
    isRunning := true;
    [** YIELD **];
    line0;
    line1;
    ...
    line40syscall;
    [** YIELD **];
    ...
    line70syscall;
    [** YIELD **];
    ...
    line100;
    isRunning := false;
    [** unlock **];
  }
}

Module MD4 {
  LS: Type;
  local_state: LS := initial_local_state;
  isRunning: bool := false;

  fun FUN: ? -> ? {
    [** lock **];
    assert!(isRunning == false);
    isRunning := true;
    [** YIELD **];
    line0;
    line1;
    ...
    line40syscall;
    local_state_remember = local_state;
    [** YIELD **];
    guarantee!(local_state_remember == local_state);
    ...
    line70syscall;
    local_state_remember = local_state;
    [** YIELD **];
    guarantee!(local_state_remember == local_state);
    ...
    line100;
    isRunning := false;
    [** unlock **];
  }
}

// INIT은 memory-irrelavant 하지는 않음.
// MD-FUN가 memory-irrelevant하고, local_state가 안변했다면, YIELD 지울 수 있는 meta-theory

Module MD5 {
  LS: Type;
  local_state: LS := initial_local_state;

  fun FUN: ? -> ? {
    [** lock **];
    line0;
    line1;
    ...
    line40syscall;
    ...
    line70syscall;
    ...
    line100;
    [** unlock **];
  }
}
