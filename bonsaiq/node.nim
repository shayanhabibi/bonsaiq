import bonsaiq/spec

template nodePadding: int =
  cacheLineSize - sizeof(pointer) * 4 - sizeof(uint) * 2 - 2

type
  Node* = object # Cache line aligned
    parent*: ptr Node
    left*: ptr Node
    next*: ptr Node
    right*: ptr Node
    value*: uint
    key*: uint
    inserting*: bool
    parentDirection*: Direction
    padding: array[nodePadding, char]

template getMark*(tptr: ptr Node): untyped = cast[uint](cast[uint](tptr) and flagMask)
template address*(tptr: ptr Node): untyped = cast[ptr Node](cast[uint](tptr) and ptrMask)

template markDelete*(v: ptr Node): ptr Node = cast[ptr Node](cast[int](v) or deleteFlag)
template markInsert*(v: ptr Node): ptr Node = cast[ptr Node](cast[int](v) or insertFlag)
template markLeaf*(v: ptr Node): ptr Node = cast[ptr Node](cast[int](v) or leafFlag)

proc createNode*(): ptr Node =
  result = createShared Node
  result.parent = cast[ptr Node](0)
  result.left = cast[ptr Node](0)
  result.next = cast[ptr Node](0)
  result.right = cast[ptr Node](0)

proc freeNode*(n: ptr Node | pointer) =
  freeShared(cast[ptr Node](n))