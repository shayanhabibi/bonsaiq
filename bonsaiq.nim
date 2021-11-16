## BonsaiQ
## ====================
## 
## A lock-free linearizable priority queue algorithm by Adones Rukundo
## and Philippas Tsigas as TSLQueue (Tree-Search-List Queue) implemented
## and adapted in nim.
##
## The BonsaiQ is a combination of two structures; a binary external search
## tree and an ordered linked list.

import bonsaiq/spec
import bonsaiq/node
from std/random import rand
import nuclear
import nuclear/atomics as natomics
export nuclear

template tslPadding*: int =
  cacheLineSize - sizeof(ptr Node) * 2 - sizeof(uint) - sizeof(uint32)
template infoPadding*: int =
  cacheLineSize - sizeof(ptr Node) * 4 - 2

type
  BonsaiQ*[T] = ref object
    head: nuclear Node
    root: nuclear Node
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
  when operationMark is uint:
    operationMark = parentNode.next[].getMark
  else:
    operationMark = parentNode.next
  parentNodeLeft = parentNode.left[].cptr
  childNode = cast[nuclear Node](parentNodeLeft.address)
  when childMark is uint:
    childMark = parentNodeLeft.getMark
  else:
    childMark = parentNodeLeft.getMark
  parentDirection = LeftDir

template readRight(): untyped {.dirty.} =
  when operationMark is uint:
    operationMark = parentNode.next[].getMark
  else:
    operationMark = parentNode.next
  parentNodeRight = parentNode.right[].cptr
  childNode = cast[nuclear Node](parentNodeRight.address)
  when childMark is uint:
    childMark = parentNodeRight.getMark
  else:
    childMark = parentNodeRight
  parentDirection = RightDir

template traverse(): untyped {.dirty.} =
  if key <= parentNode.key[]:
    when operationMark is uint:
      operationMark = parentNode.next[].getMark
    else:
      operationMark = parentNode.next
    parentNodeLeft = parentNode.left[].cptr
    childNode = cast[nuclear Node](parentNodeLeft.address)
    when childMark is uint:
      childMark = parentNodeLeft.getMark
    else:
      childMark = parentNodeLeft
      parentDirection = LeftDir
  else:
    when operationMark is uint:
      operationMark = parentNode.next[].getMark
    else:
      operationMark = parentNode.next
    parentNodeRight = parentNode.right[].cptr
    childNode = cast[nuclear Node](parentNodeRight.address)
    when childMark is uint:
      childMark = parentNodeRight.getMark
    else:
      childMark = parentNodeRight
      parentDirection = RightDir


proc newBonsaiQ*[T](numThreads: int): BonsaiQ[T] =
  result = new BonsaiQ[T]

  var head = createNode()
  var root = createNode()
  var dummy = createNode()

  dummy.left[] = head
  dummy.right[] = markLeaf(dummy)
  dummy.parent[] = root


  head.next[] = dummy

  root.left[] = dummy
  root.key[] = 1'u
  result[].head.nuclearAddr()[] = head
  result[].root.nuclearAddr()[] = root
  result[].threadNum.nuclearAddr()[] = numThreads
  result[].delScale.nuclearAddr()[] = cast[uint32](numThreads.uint * 100.uint)

proc pqSize[T](tsl: BonsaiQ[T]): uint32 =
  var prevNode, leafNode, nextLeaf, head: ptr Node
  head = tsl.head.cptr

  leafNode = head[].next.cptr.address
  nextLeaf = leafNode[].next.cptr.address

  while not leafNode.isNil:
    nextLeaf = leafNode[].next.cptr.address
    if leafNode[].next.cptr.getMark == 0'u and not nextLeaf.isNil:
      inc result
    leafNode = leafNode[].next.cptr.address()
    
template tryHelpingInsert(newNode: nuclear Node) =
  var parentDirection: Direction
  var casNode1, casNode2: ptr Node
  parentDirection = newNode.parentDirection[]
  casNode1 = cptr(newNode.parent[])
  casNode2 = cptr(newNode.left[])

  if parentDirection == LeftDir and newNode.inserting[]:
    if newNode.inserting[]:
      discard casNode1.left.addr.compareExchange(casNode2, newNode)
      if newNode.inserting[]:
        newNode.inserting[] = false
  elif parentDirection == RightDir and newNode.inserting[]:
    if newNode.inserting[]:
      discard casNode1.right.addr.compareExchange(casNode2, newNode)
      if newNode.inserting[]:
        newNode.inserting[] = false


proc physicalDelete[T](tsl: BonsaiQ[T], dummyNode: nuclear Node) =
  var childNode, childNext, grandParentNode, parentNode, root: nuclear Node
  root = tsl[].root.nuclearAddr()[]
  var parentDirection: Direction
  var clear: uint8
  var parentNodeLeft, parentNodeRight, casVal, currentNext, markedNode: ptr Node
  var operationMark, childMark: uint

  parentNode = root
  childNode = root.left[]
  
  block finish:
    while true:
      if operationMark == deleteFlag:
        readRight()
        markedNode = parentNode.cptr
        while true:
          if operationMark == deleteFlag:
            if childMark != leafFlag:
              parentNode = childNode
              readRight()
              continue
            else:
              childNext = childNode.next[]
              if childNext.inserting[] and
                  childNext.parent[] == parentNode:
                tryHelpingInsert(childNext)
              elif parentNode.right[] == childNode.markLeaf:
                if grandParentNode.key[] != 0'u:
                  grandParentNode.key[] = 0'u
                  break finish
              readRight()
              continue
          else:
            if not grandParentNode.next[].getMark != 0'u:
              if grandParentNode.left[].cptr == markedNode:
                if grandParentNode.left.compareExchange(markedNode, parentNode):
                  readLeft()
                  break
                parentNode = grandParentNode
                readLeft()
                break
            break finish
      else:
        if childMark != leafFlag:
          if parentNode.key[] == 0'u or parentNode == dummyNode:
            if parentNode.key[] != 0'u:
              parentNode.key[] = 0'u
            break finish
          grandParentNode = parentNode
          parentNode = childNode
          readLeft()
          continue
        else:
          currentNext = childNode.next[].cptr
          childNext = cast[nuclear Node](currentNext.address)
          if currentNext.getMark != 0'u:
            if childNext.inserting[] and
                childNext.parent[] == parentNode:
              tryHelpingInsert(childNext)
            elif parentNode.left[] == childNode.markLeaf:
              if childNext.key[] != 0'u:
                childNext.key[] = 0'u
              break finish
            readLeft()
            continue


proc insertSearch[T](tsl: BonsaiQ[T], key: uint): RecordInfo =
  # Locates an active preceding leaf node to the key, together with
  # that leafs parent and its succeeding leaf.
  var childNode, grandParentNode, parentNode, root: nuclear Node
  var childNext, currentNext, parentNodeRight, parentNodeLeft, markedNode: ptr Node
  var parentDirection: Direction
  var operationMark: Nuclear[Nuclear[Node]]
  var childMark: ptr Node

  root = tsl[].root.nuclearAddr()[]

  var insSeek = RecordInfo()

  parentNode = root
  childNode = root.left[]
  while true:
    if not operationMark.isNil and operationMark[].getMark == deleteFlag.uint:
      readRight()
      markedNode = parentNode.cptr

      while true:
        if operationMark[].getMark == deleteFlag.uint:
          if childMark.getMark != leafFlag.uint:
            parentNode = childNode
            readRight()
            continue
          else:
            parentNode = childNode.next[].address
            readRight()
            break
        else:
          if rand(tsl) < insertCleanRate:
            if not (grandParentNode.next[].getMark != 0'u) and
                grandParentNode.left[].cptr == markedNode:
              discard grandParentNode.left.compareExchange(markedNode, parentNode)
          traverse()
          break
      continue
    if childMark.getMark != leafFlag:
      grandParentNode = parentNode
      parentNode = childNode
      traverse()
    else:
      currentNext = childNode.next[].cptr
      childNext = currentNext.address
      if currentNext.getMark != 0'u:
        # REVIEW GO_NEXT
        parentNode = cast[nuclear Node](childNext)
        readRight()
      elif (not childNext.isNil()) and childNext[].inserting:
        tryHelpingInsert(cast[nuclear Node](childNext))
        parentNode = cast[nuclear Node](childNext)
        traverse()
      elif (not childNext.isNil()) and childNext[].key == key:
        insSeek.duplicate = DuplDir
        return insSeek
      elif (parentDirection == LeftDir and
          parentNode.left[] == childNode.markLeaf()) or
          (parentDirection == RightDir and
          parentNode.right[] == childNode.markLeaf()):
        insSeek.child = childNode.cptr
        insSeek.casNode1 = parentNode.cptr
        insSeek.casNode2 = childNode.markLeaf().cptr
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
    when T is ref:
      let res = cast[T](x)
      GC_unref res
      res
    else:
      cast[T](x)
    
  var leafNode, nextLeaf, head: nuclear Node
  var xorNode, currentNext, headItemNode, newHead: ptr Node
  var value: uint

  # The operation will start from the head and perform a linear search
  # on the list until a an active dummy node is located.
  head = tsl.head

  headItemNode = head.next[].cptr
  leafNode = cast[nuclear Node](headItemNode)

  if previousHead == leafNode.cptr:
    leafNode = cast[nuclear Node](previousDummy)
  else:
    previousHead = headItemNode

  # Begin linear search loop of list
  while true:
    currentNext = leafNode.next[].cptr
    nextLeaf = cast[nuclear Node](currentNext)
    if nextLeaf.isNil:
      previousDummy = leafNode.cptr
      break
    if currentNext.getMark != 0'u:
      leafNode = nextLeaf
    else:
      # Global Atomic Update I
      # Logically delete the dummy by settings the next pointers
      # delete flag to true.
      xorNode = leafNode.next.fetchXor(1, moAcquire).cptr # REVIEW - wouldnt this turn off a deleted node though? :/
      # Success of this operation linearizes operations
      if xorNode.getMark == 0'u:
        # The suceeding leaf value is read; and that leaf becomes the new dummy
        # node.
        value = xorNode.address()[].value
        previousDummy = xorNode
        if tsl.rand >= physicalDeleteRate:
          # Random selection of operations based on the number of concurrent
          # threads will ignore the physical deletion of logically deleted nodes
          # and simply return the value received.
          result = value.ready
          break
        if head.next[].cptr == headItemNode:
          # Global Atomic Update II
          # Physically delete the logically deleted dummy from the list
          # by updating the head nodes next pointer from the deleted dummy
          # to the new active dummy
          if head.next.compareExchange(headItemNode, xorNode):
            previousHead = xorNode
            if xorNode[].key != 0'u:
              xorNode[].key = 0'u
              # Global Atomic Update III
              # Within the physical delete operation, we update the closest
              # active ancestors left child pointer to point to the active dummy.
              # It is likely that is already the case, in which case it is ignored.
              physicalDelete(tsl, cast[nuclear Node](xorNode))
              nextLeaf = cast[nuclear Node](headItemNode)
              while nextLeaf.cptr != xorNode:
                currentNext = nextLeaf.cptr
                nextLeaf = nextLeaf.next[].address
                freeNode(currentNext)
        result = value.ready
        break
      leafNode = cast[nuclear Node](xorNode.address)

      

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
  template clean: untyped =
    # This template will be used if the push fails to dec the ref count
    when T is ref:
      GC_unref val
    else:
      discard

  var value = cast[uint](val)
  var casNode1, casNode2, leafNode: nuclear Node
  var nextLeaf: ptr Node
  var parentDirection: Direction
  var insSeek: RecordInfo

  # First we create a new node that we will insert into the tree with the val
  # provided
  var newNode: nuclear Node = createNode()
  newNode.right[] = markLeaf(newNode)
  newNode.key[] = key
  newNode.value[] = value

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
    casNode1 = cast[nuclear Node](insSeek.casNode1)
    casNode2 = cast[nuclear Node](insSeek.casNode2)
    leafNode = cast[nuclear Node](insSeek.child)
    nextLeaf = insSeek.nextNode
    newNode.left[] = leafNode.markLeaf
    newNode.parentDirection[] = parentDirection
    newNode.parent[] = casNode1
    newNode.next[] = cast[nuclear Node](nextLeaf)
    newNode.inserting[] = true
    if leafNode.next[].cptr == nextLeaf:
      template casDir(casDir: Direction): untyped =
        # The node is inserted with two global linearizeable atomic updates
        if leafNode.next[].cptr == nextLeaf:
          # Atomically add the new node to the list by updating the preceding
          # leaf nodes next pointer from the old succeeding node to our newnode.
          if leafNode.next.compareExchange(nextLeaf, newNode, moAcquire):
            # Success of the previous CAS linearizes the insert operation and
            # the new node becomes active
            if newNode.inserting[]:
              # We now atomically add the new node to the tree by updating
              # the preceding parent nodes child pointer from the preceding
              # node to the new node with the leaf flag set to false.
              when casDir == RightDir:
                if casNode1.right[] == casNode2:
                  discard casNode1.right.compareExchange(casNode2, newNode, moRelease)

              elif casDir == LeftDir:
                if casNode1.left[] == casNode2:
                  discard casNode1.left.compareExchange(casNode2, newNode, moRelease)
              
              if newNode.inserting[]:
                newNode.inserting[] = false
              # The insert completes and returns true
            return true # END; SUCCESS INSERT

      if parentDirection == RightDir:
        casDir RightDir
      elif parentDirection == LeftDir:
        casDir LeftDir