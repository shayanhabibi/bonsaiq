import bonsaiq/spec
import nuclear

template nodePadding: int =
  cacheLineSize - sizeof(pointer) * 4 - sizeof(uint) * 2 - 2

type
  Node* = object # Cache line aligned
    parent*: nuclear Node
    left*: nuclear Node
    next*: nuclear Node
    right*: nuclear Node
    value*: uint
    key*: uint
    inserting*: bool
    parentDirection*: Direction
    padding: array[nodePadding, char]

template getMark*(tptr: nuclear Node): untyped = cast[uint](cast[uint](tptr) and flagMask)
template getMark*(tptr: ptr Node): untyped = cast[uint](cast[uint](tptr) and flagMask)
template address*(tptr: nuclear Node): untyped = cast[nuclear Node](cast[uint](tptr) and ptrMask)
template address*(tptr: ptr Node): untyped = cast[ptr Node](cast[uint](tptr) and ptrMask)

template markDelete*(v: nuclear Node): nuclear Node = cast[nuclear Node](cast[int](v) or deleteFlag)
template markInsert*(v: nuclear Node): nuclear Node = cast[nuclear Node](cast[int](v) or insertFlag)
template markLeaf*(v: nuclear Node): nuclear Node = cast[nuclear Node](cast[int](v) or leafFlag)

proc createNode*(): nuclear Node =
  result = nucleate Node
  result.parent[] = cast[nuclear Node](0)
  result.left[] = cast[nuclear Node](0)
  result.next[] = cast[nuclear Node](0)
  result.right[] = cast[nuclear Node](0)

proc freeNode*(n: ptr Node | Nuclear[Node] | pointer) =
  freeShared(cast[ptr Node](n))