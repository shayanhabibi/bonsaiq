## BonsaiQ
## ====================
## 
## A lock-free linearizable priority queue algorithm by Adones Rukundo
## and Philippas Tsigas as TSLQueue (Tree-Search-List Queue) implemented
## and adapted in nim.
##
## The BonsaiQ is a combination of two structures; a binary external search
## tree and an ordered linked list.

import std/volatile
export volatile

template avolatileLoad(x: untyped): untyped = x.addr.volatileLoad()
template avolatileStore(x,y: untyped): untyped = x.addr.volatileStore(y)

import bonsaiq/spec
import bonsaiq/node
from std/random import rand

template tslPadding*: int =
  cacheLineSize - sizeof(ptr Node) * 2 - sizeof(uint) - sizeof(uint32)
template infoPadding*: int =
  cacheLineSize - sizeof(ptr Node) * 4 - 2

type
  BonsaiQ*[T] = ref object
    head: ptr Node
    root: ptr Node
    threadNum: int
    delScale: uint32
    padding: array[tslPadding, char]
  
  RecordInfo = object
    child: ptr Node
    nextNode: ptr Node
    casNode1: ptr Node
    casNode2: ptr Node
    duplicate: Direction
    parentDirection: Direction
    padding: array[infoPadding, char]

var previousHead, previousDummy: ptr Node

proc rand[T](tsl: BonsaiQ[T]): uint32 {.inline.} =
  cast[uint32](rand(tsl.delScale.int))

template readLeft(): untyped {.dirty.} =
  operationMark = parentNode.next.avolatileLoad().getMark
  parentNodeLeft = parentNode.left.avolatileLoad()
  childNode = parentNodeLeft.address
  childMark = parentNodeLeft.getMark
  parentDirection = LeftDir

template readRight(): untyped {.dirty.} =
  operationMark = parentNode.next.avolatileLoad().getMark
  parentNodeRight = parentNode.right.avolatileLoad()
  childNode = parentNodeRight.address
  childMark = parentNodeRight.getMark
  parentDirection = RightDir

template traverse(): untyped {.dirty.} =
  if key <= parentNode.key.avolatileLoad():
    operationMark = parentNode.next.avolatileLoad().getMark
    parentNodeLeft = parentNode.left.avolatileLoad()
    childNode = parentNodeLeft.address
    childMark = parentNodeLeft.getMark
    parentDirection = LeftDir
  else:
    operationMark = parentNode.next.avolatileLoad().getMark
    parentNodeRight = parentNode.right.avolatileLoad()
    childNode = parentNodeRight.address
    childMark = parentNodeRight.getMark
    parentDirection = RightDir


proc newBonsaiQ*[T](numThreads: int): BonsaiQ[T] =
  result = new BonsaiQ[T]
  var head, root, dummy: ptr Node
  head = createNode()
  root = createNode()
  dummy = createNode()

  dummy.left.avolatileStore head
  dummy.right.avolatileStore markLeaf(dummy)
  dummy.parent.avolatileStore root

  head.next.avolatileStore dummy
  root.left.avolatileStore dummy
  root.key.avolatileStore 1'u
  result.head.avolatileStore head
  result.root.avolatileStore root
  result.threadNum.avolatileStore numThreads
  result.delScale.avolatileStore cast[uint32](numThreads.uint * 100.uint)

proc pqSize[T](tsl: BonsaiQ[T]): uint32 =
  var prevNode, leafNode, nextLeaf, head: ptr Node
  head = tsl.head

  leafNode = head.next.address
  nextLeaf = leafNode.next.address

  while not leafNode.isNil:
    nextLeaf = leafNode.next.address
    if leafNode.next.getMark == 0'u and not nextLeaf.isNil:
      inc result
    leafNode = leafNode.next.address()
    
proc tryHelpingInsert(newNode: ptr Node) {.inline.} =
  # newNode is volatile ptr
  var parentDirection: Direction
  var casNode1, casNode2: ptr Node

  parentDirection = newNode.parentDirection.avolatileLoad()
  casNode1 = newNode.parent.avolatileLoad()
  casNode2 = newNode.left.avolatileLoad()

  template doCAS(x: untyped): untyped =
    x.addr.atomicCompareExchangeN(casNode2.addr, newNode, false, ATOMIC_SEQ_CST, ATOMIC_SEQ_CST)

  if parentDirection == LeftDir and newNode.inserting.avolatileLoad():
    if newNode.inserting.avolatileLoad():
      discard casNode1.left.doCAS
      if newNode.inserting.avolatileLoad():
        newNode.inserting.avolatileStore false
  elif parentDirection == RightDir and newNode.inserting.avolatileLoad():
    if newNode.inserting.avolatileLoad():
      discard casNode1.right.doCAS
      if newNode.inserting.avolatileLoad():
        newNode.inserting.avolatileStore false


proc physicalDelete[T](tsl: BonsaiQ[T], dummyNode: ptr Node) =
  # DummyNode - Volatile
  var childNode, childNext, grandParentNode, parentNode, root: ptr Node # Volatile
  root = tsl.root.avolatileLoad()
  var parentDirection: Direction
  var clear: uint8
  var parentNodeLeft, parentNodeRight, casVal, currentNext, markedNode: ptr Node
  var operationMark, childMark: uint

  parentNode = root
  childNode = root.left.avolatileLoad()
  
  block finish:
    while true:
      if operationMark == deleteFlag:
        readRight()
        markedNode = parentNode
        while true:
          if operationMark == deleteFlag:
            if childMark != leafFlag:
              parentNode = childNode
              readRight()
              continue
            else:
              childNext = address(childNode.next.avolatileLoad())
              if childNext.inserting.avolatileLoad() and
                  childNext.parent.avolatileLoad() == parentNode:
                tryHelpingInsert(childNext)
              elif parentNode.right.avolatileLoad() == childNode.markLeaf:
                if grandParentNode.key.avolatileLoad() != 0'u:
                  grandParentNode.key.avolatileStore 0'u
                  break finish
              readRight()
              continue
          else:
            if not getMark(grandParentNode.next.avolatileLoad()) != 0'u:
              if grandParentNode.left.avolatileLoad() == markedNode:
                if grandParentNode.left.addr.atomicCompareExchangeN(markedNode.addr, parentNode, false, ATOMIC_SEQ_CST, ATOMIC_SEQ_CST):
                  readLeft()
                  break
                parentNode = grandParentNode
                readLeft()
                break
            break finish
      else:
        if childMark != leafFlag:
          if parentNode.key.avolatileLoad() == 0'u or parentNode == dummyNode:
            if parentNode.key.avolatileLoad() != 0'u:
              parentNode.key.avolatileStore 0'u
            break finish
          grandParentNode = parentNode
          parentNode = childNode
          readLeft()
          continue
        else:
          currentNext = childNode.next.avolatileLoad()
          childNext = currentNext.address
          if currentNext.getMark != 0'u:
            if childNext.inserting.avolatileLoad() and
                childNext.parent.avolatileLoad() == parentNode:
              tryHelpingInsert(childNext)
            elif parentNode.left.avolatileLoad() == childNode.markLeaf:
              if childNext.key.avolatileLoad() != 0'u:
                childNext.key.avolatileStore 0'u
              break finish
            readLeft()
            continue


proc insertSearch[T](tsl: BonsaiQ[T], key: uint): RecordInfo =
  # Locates an active preceding leaf node to the key, together with
  # that leafs parent and its succeeding leaf.
  var childNode, grandParentNode, parentNode, root: ptr Node # Volatile
  var childNext, currentNext, parentNodeRight, parentNodeLeft, markedNode: ptr Node
  var parentDirection: Direction
  var operationMark, childMark {.volatile.}: uint
  childMark = 0'u

  root = tsl.root.avolatileLoad()

  var insSeek = RecordInfo()

  parentNode = root
  childNode = root.left.avolatileLoad
  while true:
    if operationMark == deleteFlag.uint:
      readRight()
      markedNode = parentNode

      while true:
        if operationMark == deleteFlag.uint:
          if childMark != leafFlag.uint:
            parentNode = childNode
            readRight()
            continue
          else:
            parentNode = address(childNode.next.avolatileLoad())
            readRight()
            break
        else:
          if rand(tsl) < insertCleanRate:
            if not (grandParentNode.next.avolatileLoad().getMark != 0'u) and
                grandParentNode.left.avolatileLoad() == markedNode:
              discard grandParentNode.left.addr.atomicCompareExchangeN(markedNode.addr, parentNode, false, ATOMIC_SEQ_CST, ATOMIC_SEQ_CST) # FIXME
          traverse()
          break
      continue
    if childMark != leafFlag:
      grandParentNode = parentNode
      parentNode = childNode
      traverse()
    else:
      currentNext = childNode.next.avolatileLoad()
      childNext = currentNext.address
      if currentNext.getMark != 0'u:
        # REVIEW GO_NEXT
        parentNode = childNext
        readRight()
      elif (not childNext.isNil()) and childNext.inserting:
        tryHelpingInsert(childNext)
        parentNode = childNext
        traverse()
      elif (not childNext.isNil()) and childNext.key == key:
        insSeek.duplicate = DuplDir
        return insSeek
      elif (parentDirection == LeftDir and
          parentNode.left.avolatileLoad() == childNode.markLeaf()) or
          (parentDirection == RightDir and
          parentNode.right.avolatileLoad() == childNode.markLeaf()):
        insSeek.child = childNode
        insSeek.casNode1 = parentNode
        insSeek.casNode2 = childNode.markLeaf()
        insSeek.nextNode = childNext
        insSeek.parentDirection = parentDirection
        return insSeek
      else:
        traverse()

proc pop*[T](tsl: BonsaiQ[T]): T =
  ## Remove the object from the queue with the lowest key value.
  runnableExamples:
    type
      Obj = ref object
        field1: int
        field2: int

    var myobj = Obj(field1: 5, field2: 19)
    var myobj2 = Obj(field1: 3, field2: 12)
    var myobj3 = Obj(field1: 0, field2: 1)
    var tsl = newBonsaiQ[Obj](1)
    doAssert tsl.push(2, myobj) == true
    doAssert tsl.push(1, myobj2) == true
    doAssert tsl.push(3, myobj3) == true
    doAssert tsl.pop() == myobj2
    
  template ready(x: uint): T =
    # Template is used to prepare the received value from the node
    # by converting it into its original type and decreasing its
    # ref count if it is a ref
    atomicThreadFence(ATOMIC_ACQUIRE)
    when T is ref:
      let res = cast[T](x)
      GC_unref res
      res
    else:
      cast[T](x)
    
  var leafNode, nextLeaf, head: ptr Node # Volatile
  var xorNode, currentNext, headItemNode, newHead: ptr Node
  var value: uint

  # The operation will start from the head and perform a linear search
  # on the list until a an active dummy node is located.
  head = tsl.head.avolatileLoad()

  headItemNode = head.next.avolatileLoad()
  leafNode = headItemNode

  if previousHead == leafNode:
    leafNode = previousDummy
  else:
    previousHead = headItemNode

  # Begin linear search loop of list
  while true:
    currentNext = leafNode.next.avolatileLoad()
    nextLeaf = currentNext
    if nextLeaf.isNil:
      previousDummy = leafNode
      break
    if currentNext.getMark != 0'u:
      leafNode = nextLeaf
    else:
      # Global Atomic Update I
      # Logically delete the dummy by settings the next pointers
      # delete flag to true.
      xorNode = cast[ptr Node](cast[ptr int](leafNode.next.addr).atomicFetchXor(1, ATOMIC_ACQUIRE)) # wouldnt this turn off a deleted node though? :/
      # Success of this operation linearizes operations
      if xorNode.getMark == 0'u:
        # The suceeding leaf value is read; and that leaf becomes the new dummy
        # node.
        value = xorNode.value
        previousDummy = xorNode
        if tsl.rand >= physicalDeleteRate:
          # Random selection of operations based on the number of concurrent
          # threads will ignore the physical deletion of logically deleted nodes
          # and simply return the value received.
          result = value.ready
          break
        if head.next.avolatileLoad() == headItemNode:
          # Global Atomic Update II
          # Physically delete the logically deleted dummy from the list
          # by updating the head nodes next pointer from the deleted dummy
          # to the new active dummy
          if head.next.addr.atomicCompareExchangeN(headItemNode.addr, xorNode, false, ATOMIC_SEQ_CST, ATOMIC_SEQ_CST): # FIXME
            previousHead = xorNode
            if xorNode.key != 0'u:
              xorNode.key = 0'u
              # Global Atomic Update III
              # Within the physical delete operation, we update the closest
              # active ancestors left child pointer to point to the active dummy.
              # It is likely that is already the case, in which case it is ignored.
              physicalDelete(tsl, xorNode)
              nextLeaf = headItemNode
              while nextLeaf != xorNode:
                currentNext = nextLeaf
                nextLeaf = address(nextLeaf.next.avolatileLoad())
                freeNode(currentNext)
        result = value.ready
        break
      leafNode = xorNode.address

      

proc push*[T](tsl: BonsaiQ[T]; vkey: Natural, val: T): bool =
  ## Try push an object onto the queue with a key for priority.
  ## Pops will remove the object with the lowest vkey first.
  ## You cannot have duplicate keys (for the moment).
  runnableExamples:
    type
      Obj = ref object
        field1: int
        field2: int

    var myobj = Obj(field1: 5, field2: 19)

    var tsl = newBonsaiQ[Obj](1)
    doAssert tsl.push(1, myobj) == true
    doAssert tsl.pop() == myobj
  
  var key = vkey.uint
  # Begin by increasing the ref count of the val if it is a ref
  when T is ref:
    GC_ref val
  atomicThreadFence(ATOMIC_RELEASE)
  template clean: untyped =
    # This template will be used if the push fails to dec the ref count
    when T is ref:
      GC_unref val
    else:
      discard

  var value = cast[uint](val)
  var casNode1, casNode2, leafNode: ptr Node # Volatile
  var nextLeaf: ptr Node
  var parentDirection: Direction
  var insSeek: RecordInfo

  # First we create a new node that we will insert into the tree with the val
  # provided
  var newNode = createNode() # Volatile
  newNode.right.avolatileStore markLeaf(newNode)
  newNode.key.avolatileStore key
  newNode.value.avolatileStore value

  # Begin insert-loop
  while true:
    # Nullify any preceding values of our casNodes
    casNode1 = nil
    casNode2 = nil
    # Begin by performing an insertSearch with the vkey
    insSeek = insertSearch(tsl, key) # GOTO insertSearch
    # insSeek will contain the active preceding leaf, its parent, and
    # its succeeding leaf nodes.
    if insSeek.duplicate == DuplDir:
      # If however the key provided is a duplicate of a key in the list,
      # the insert function has failed and we deallocate the node
      freeNode(newNode)
      clean() # <- derefs val if it is a ref
      return false  # END; FAILED INSERT
    elif insSeek.child.isNil:
      continue
    # We now prepare to insert the new node
    parentDirection = insSeek.parentDirection
    casNode1 = insSeek.casNode1
    casNode2 = insSeek.casNode2

    leafNode = insSeek.child # Insertion point
    nextLeaf = insSeek.nextNode
    # Prepare internal node and its children
    newNode.left.avolatileStore leafNode.markLeaf
    newNode.parentDirection.avolatileStore parentDirection
    newNode.parent.avolatileStore casNode1
    newNode.next.avolatileStore nextLeaf
    newNode.inserting.avolatileStore true
    if leafNode.next.avolatileLoad == nextLeaf:
      template casDir(casDir: Direction): untyped =
        # The node is inserted with two global linearizeable atomic updates
        if leafNode.next.avolatileLoad == nextLeaf:
          # Atomically add the new node to the list by updating the preceding
          # leaf nodes next pointer from the old succeeding node to our newnode.
          if leafNode.next.addr.atomicCompareExchangeN(nextLeaf.addr, newNode, false, ATOMIC_ACQUIRE, ATOMIC_ACQUIRE): # FIXME
            # Success of the previous CAS linearizes the insert operation and
            # the new node becomes active
            if newNode.inserting.avolatileLoad:
              # We now atomically add the new node to the tree by updating
              # the preceding parent nodes child pointer from the preceding
              # node to the new node with the leaf flag set to false.
              when casDir == RightDir:
                if casNode1.right.avolatileLoad == casNode2:
                  discard casNode1.right.addr.atomicCompareExchangeN(casNode2.addr, newNode, false, ATOMIC_RELEASE, ATOMIC_RELEASE)

              elif casDir == LeftDir:
                if casNode1.left.avolatileLoad == casNode2:
                  discard casNode1.left.addr.atomicCompareExchangeN(casNode2.addr, newNode, false, ATOMIC_RELEASE, ATOMIC_RELEASE)
              
              if newNode.inserting.avolatileLoad:
                newNode.inserting.avolatileStore false
              # The insert completes and returns true
            return true # END; SUCCESS INSERT

      if parentDirection == RightDir:
        casDir RightDir
      elif parentDirection == LeftDir:
        casDir LeftDir