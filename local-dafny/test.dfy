module HelloWorld {

  ghost function max(x: int, y: int) : (res: int) 
    ensures res == x || res == y
    ensures res >= x && res >= y
  {
    if x > y then x else y
  }
}
