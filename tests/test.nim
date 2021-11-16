import std/osproc
import std/strutils
import std/logging
import std/atomics
import std/os
import std/macros

import balls
import cps

import disrubscok

const
  continuationCount = 10
let
  threadCount = 1

type
  C = ref object of Continuation

addHandler newConsoleLogger()
setLogFilter:
  when defined(danger):
    lvlNotice
  elif defined(release):
    lvlInfo
  else:
    lvlDebug

var q: TslQueue[Continuation]

proc runThings() {.thread.} =
  {.cast(gcsafe).}:
    while true:
      var job = pop q
      if job.dismissed:
        break
      else:
        while job.running:
          job = trampoline job

proc enqueue(c: C): C {.cpsMagic.} =
  var x: int
  while not q.push(x.int, c):
    echo x
    inc x
var counter {.global.}: Atomic[int]

# try to delay a reasonable amount of time despite platform
when defined(windows):
  proc noop(c: C): C {.cpsMagic.} =
    c
proc doContinualThings() {.cps: C.} =
  enqueue()
  noop()
  enqueue()
  discard counter.fetchAdd(1)

template expectCounter(n: int): untyped =
  ## convenience
  try:
    check counter.load == n
  except Exception:
    checkpoint " counter: ", load counter
    checkpoint "expected: ", n
    raise

suite "disrubscok":
  block:
    ## creation and initialization of the queue

    # Moment of truth
    q = newTslQueue[Continuation](threadCount)

  block:
    ## run some continuations through the queue in another thread
    when defined(danger): skip "boring"
    var thr: Thread[void]
    proc main1() =
      counter.store 0
      for i in 0 ..< continuationCount:
        var c = whelp doContinualThings()
        discard enqueue c
      createThread(thr, runThings)
      joinThread thr
      expectCounter continuationCount
    main1()

  block:
    ## run some continuations through the queue in many threads
    when not defined(danger): skip "slow"
    var threads: seq[Thread[void]]
    newSeq(threads, threadCount)

    counter.store 0
    # If `loonyDebug` is defined this will output number of nodes you started
    # with - the number of nodes you end with (= non-deallocated nodes)
    proc main2()=
      for i in 0 ..< continuationCount:
        var c = whelp doContinualThings()
        discard enqueue c
    main2()
    checkpoint "queued $# continuations" % [ $continuationCount ]

    proc main3()=
      for thread in threads.mitems:
        createThread(thread, runThings)
    main3()
    checkpoint "created $# threads" % [ $threadCount ]
    
    proc main4()=
      for thread in threads.mitems:
        joinThread thread
    main4()
    checkpoint "joined $# threads" % [ $threadCount ]


    expectCounter continuationCount