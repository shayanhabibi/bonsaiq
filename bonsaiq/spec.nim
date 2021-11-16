# import wtbanland/cacheline # Not ready to be used yet; just use a const
const cacheLineSize* = 64

const
  deleteFlag* = 1                      # 1
  insertFlag* = 1 shl 1              # 2
  leafFlag* = deleteFlag or insertFlag # 3

  flagMask* = ((1 shl 2) - 1).uint
  ptrMask* = high(uint) xor flagMask

  physicalDeleteRate*: uint32 = 1
  insertCleanRate*: uint32 = 50

type
  Direction* = enum
    LeftDir, RightDir, DuplDir

template natShl(val: SomeInteger): untyped =
  (1 shl val)
template subShl(val: SomeInteger): untyped =
  (1 shl val) - 1

const
  MemAlign* = # also minimal allocatable memory block
    when defined(useMalloc):
      when defined(amd64): natShl 4 # 16
      else: natShl 3  # 8
    else: natShl 4  # 16