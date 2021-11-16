import bonsaiq

const threadCount = 16

type
  Obj = ref object
    field1: int
    field2: int

var x {.threadvar.}: int

var myobj = Obj(field1: 5, field2: 19)
var myobj2 = Obj(field1: 3, field2: 12)
var myobj3 = Obj(field1: 0, field2: 1)
var tsl {.global.} = newBonsaiQ[Obj](1)
doAssert tsl.push(2, myobj) == true
doAssert tsl.push(1, myobj2) == true
doAssert tsl.push(3, myobj3) == true

import os
proc doStuff() {.thread.} =
  {.cast(gcsafe).}:
    echo getThreadId()
    while x < 100:
      var obj = tsl.pop()
      echo getThreadId()
      if not obj.isNil:
        x = obj.field2
        echo x, " ", getThreadId()
        discard tsl.push(x + 1, (obj.field2 = x + 1; obj))
      else:
        echo "missed"
        x = 100

var threads: seq[Thread[void]]
newSeq(threads, threadCount)

for thread in threads.mitems:
  createThread(thread, doStuff)

while x < 100:
  var obj = new Obj
  obj.field1 = (inc x; x)
  obj.field2 = (inc x; x)
  discard tsl.push(x, obj)
  if x >= 90:
    var obj2 = new Obj
    obj2.field2 = 1
    echo tsl.push(1, obj2)
    # var obj3 = tsl.pop()
    # if not obj3.isNil:
    #   var y = obj3.field2
    #   echo y, " ", getThreadId()
    #   discard tsl.push(y + 1, (obj.field2 = y + 1; obj3))
    # else:
    #   echo "missed"
joinThreads(threads)
echo "done"

# type
#   Obj = ref object
#     field1: int
#     field2: int

# var myobj = Obj(field1: 5, field2: 19)

# var tsl = newBonsaiQ[Obj](1)
# doAssert tsl.push(1, myobj) == true
# doAssert tsl.pop() == myobj

# var tsl = newBonsaiQ[int](5)

# echo tsl.push(5, 10)
# echo tsl.push(2, 5)
# echo tsl.push(3, 10)
# echo tsl.push(7, 5)
# echo tsl.push(10, 10)
# echo tsl.pop()
# echo tsl.push(2, 5)
# echo tsl.push(2, 10)
# echo tsl.pop()
# echo tsl.pop()
# echo tsl.pop()
# echo tsl.pop()
