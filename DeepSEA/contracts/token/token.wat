(module
  (type (;0;) (func (param ) (result i32)))
  (type (;1;) (func (param ) (result i32)))
  (type (;2;) (func (param i32) (result i32)))
  (type (;3;) (func (param i32 i32) (result i32)))
  (import  "ethereum" "getAddress"  (func $f0 (param i32) (result )))
  (import  "ethereum" "getExternalBalance"  (func $f1 (param i32 i32) (result )))
  (import  "ethereum" "getBlockHash"  (func $f2 (param i64 i32) (result i32)))
  (import  "ethereum" "callDataCopy"  (func $f4 (param i32 i32 i32) (result )))
  (import  "ethereum" "getCallDataSize"  (func $f5 (param ) (result i32)))
  (import  "ethereum" "callDelegate"  (func $f7 (param i64 i32 i32 i32) (result i32)))
  (import  "ethereum" "storageStore"  (func $f8 (param i32 i32) (result )))
  (import  "ethereum" "storageLoad"  (func $f9 (param i32 i32) (result )))
  (import  "ethereum" "getCaller"  (func $f10 (param i32) (result )))
  (import  "ethereum" "getCallValue"  (func $f11 (param i32) (result )))
  (import  "ethereum" "getBlockCoinbase"  (func $f14 (param i32) (result i32)))
  (import  "ethereum" "getBlockDifficulty"  (func $f16 (param i32) (result )))
  (import  "ethereum" "getGasLeft"  (func $f19 (param ) (result i64)))
  (import  "ethereum" "getBlockGasLimit"  (func $f20 (param ) (result i64)))
  (import  "ethereum" "getTxGasPrice"  (func $f21 (param i32) (result )))
  (import  "ethereum" "log"  (func $f22 (param i32 i32 i32 i32 i32 i32 i32) (result )))
  (import  "ethereum" "getBlockNumber"  (func $f23 (param ) (result i64)))
  (import  "ethereum" "getTxOrigin"  (func $f24 (param i32) (result )))
  (import  "ethereum" "useGas"  (func $f25 (param i64) (result )))
  (import  "ethereum" "getBlockTimestamp"  (func $f27 (param ) (result i64)))
  (import  "ethereum" "revert"  (func $f28 (param i32 i32) (result )))
  (import  "ethereum" "returnDataSize"  (func $f29 (param ) (result i32)))
  (import  "ethereum" "returnDataCopy"  (func $f30 (param i32 i32 i32) (result )))
  (import  "ethereum" "call"  (func $f3 (param i64 i32 i32 i32 i32) (result i32)))
  (import  "ethereum" "finish"  (func $finish (param i32 i32) (result )))
  (memory 1)
  (data (i32.const 0) "0")
  (data (i32.const 256) "0")
  (data (i32.const 512) "0")
  (data (i32.const 768) "0")
  (data (i32.const 1024) "0")
  (data (i32.const 1280) "0")
  (data (i32.const 1536) "0")
  (data (i32.const 1792) "0")
  (data (i32.const 2048) "0")
  (data (i32.const 2304) "0")
  (global (mut i32) (i32.const 0))  (global (mut i32) (i32.const 0))  (global (mut i32) (i32.const 0))
  (export "memory" (memory 0))
  (export "main" (func $main))
  (func $f128 (param $0 i32) (param $1 i32) (result i32)
    (local $2 i32)
    (local $3 i32)
    (local.set $3
    (select
      (local.get $0)
      (i32.const 1)
      (i32.and
      (local.get $1)
      (i32.const 1)
      )
    )
    )
    (block $label$0
    (br_if $label$0
      (i32.eqz
      (local.tee $1
        (i32.shr_s
        (local.get $1)
        (i32.const 1)
        )
      )
      )
    )
    (loop $label$1
      (local.set $3
      (i32.mul
        (select
        (local.tee $0
          (i32.mul
          (local.get $0)
          (local.get $0)
          )
        )
        (i32.const 1)
        (i32.and
          (local.get $1)
          (i32.const 1)
        )
        )
        (local.get $3)
      )
      )
      (local.set $1
      (local.tee $2
        (i32.shr_s
        (local.get $1)
        (i32.const 1)
        )
      )
      )
      (br_if $label$1
      (local.get $2)
      )
    )
    )
    (local.get $3))
  (func $f129 (param $p0 i32) (param $p1 i32) (result i32) 
      local.get 0
    )
  (func $f130 (param $p0 i32) (param $p1 i32) (result i32) 
      local.get 0
    )
  (func $f131 (param $p0 i32) (param $p1 i32) (result i32) 
      local.get 0
    )
  (func $f132 (param $p0 i32) (result i32)
    local.get $p0
    i32.const -1
    i32.xor)
  (func $set_returndata (param $value i32) (result )
    i32.const 256 ;; offset to store
    local.get $value ;; valut to store
    i32.store
  )
  (func $fallback (param ) (result) 
    i32.const 256
    i32.const 4
    call $f28
    )
  (func $chendian32 (param $p0 i32) (result i32)
    local.get $p0
    i32.const 24
    i32.shl
    local.get $p0
    i32.const 8
    i32.shl
    i32.const 16711680
    i32.and
    i32.or
    local.get $p0
    i32.const 8
    i32.shr_u
    i32.const 65280
    i32.and
    local.get $p0
    i32.const 24
    i32.shr_u
    i32.or
    i32.or)
  (func $main (param ) (result )
    call $f5
    global.set 0
    global.get 0
    i32.const 3
    i32.le_u
    if 
      i32.const 21
      call $set_returndata
      call $fallback
    else 
      nop
    end
    global.get 0
    i32.const 4
    i32.sub
    global.set 0
    i32.const 4
    global.set 1
    i32.const 768
    i32.const 0
    i32.const 4
    call $f4
    i32.const 768
    i32.load
    call $chendian32
    global.set 2
    global.get 2
    i32.const 0x18160ddd
    i32.eq
    if 
      global.get 0
      i32.const 0
      i32.eq
      i32.eqz
      if 
        i32.const 220 
        call $set_returndata
        call $fallback
      else 
        nop
      end
      i32.const 32 ;; 4 + 7 * 4 = 32, setting offset exclude name
      global.set 1

      (call $f257)
      global.set 1
      i32.const 256
      global.get 1
      i32.store
      i32.const 256
      i32.const 4
      (call $finish)
    else
    global.get 2
    i32.const 0x70a08231
    i32.eq
    if 
      global.get 0
      i32.const 32
      i32.eq
      i32.eqz
      if 
        i32.const 221 
        call $set_returndata
        call $fallback
      else 
        nop
      end
      i32.const 32 ;; 4 + 7 * 4 = 32, setting offset exclude name
      global.set 1
      i32.const 768
      global.get 1
      i32.const 4
      call $f4
      i32.const 768
      i32.load ;; load argument, which is i32
      call $chendian32
      (i32.add (global.get 1) (i32.const 32)) ;; + 8 * 4 = + 32
      (global.set 1)
      (call $f258)
      global.set 1
      i32.const 256
      global.get 1
      i32.store
      i32.const 256
      i32.const 4
      (call $finish)
    else
    global.get 2
    i32.const 0xa9059cbb
    i32.eq
    if 
      global.get 0
      i32.const 64
      i32.eq
      i32.eqz
      if 
        i32.const 222 
        call $set_returndata
        call $fallback
      else 
        nop
      end
      i32.const 32 ;; 4 + 7 * 4 = 32, setting offset exclude name
      global.set 1
      i32.const 768
      global.get 1
      i32.const 4
      call $f4
      i32.const 768
      i32.load ;; load argument, which is i32
      call $chendian32
      (i32.add (global.get 1) (i32.const 32)) ;; + 8 * 4 = + 32
      (global.set 1)
      i32.const 768
      global.get 1
      i32.const 4
      call $f4
      i32.const 768
      i32.load ;; load argument, which is i32
      call $chendian32
      (i32.add (global.get 1) (i32.const 32)) ;; + 8 * 4 = + 32
      (global.set 1)
      (call $f259)
      global.set 1
      i32.const 256
      global.get 1
      i32.store
      i32.const 256
      i32.const 4
      (call $finish)
    else
      i32.const 22
      call $set_returndata
      (call $fallback)
      end
      end
      end

  )
  (func $constructor (type 0)
    (local $l0 i32)
    i32.const 0x00
    i32.const 768
    call $f10
    i32.const 768
    i32.load
    global.set 0
    global.set 1
    i32.const 0
    i32.const 9
    i32.store
    i32.const 512
    i32.const 0
    i32.store
    i32.const 256
    global.get 0
    i32.store
    i32.const 260
    global.get 1
    i32.store
    i32.const 100
    i64.extend_i32_u
    i32.const 0
    i32.const 512
    i32.const 256
    i32.const 8
    call $f3
    i32.const 768
    i32.const 0
    call $f29
    call $f30
    i32.const 768
    i32.load
    global.set 0
    global.set 1
    i32.const 0
    global.get 0
    global.get 1
    select
    global.set 0
    i32.const 1024
    global.get 0
    i32.store
    i32.const 0x0186a0
    global.set 0
    i32.const 512
    global.get 0
    i32.store
    i32.const 1024
    i32.const 512
    call $f8
    i32.const 0x00
    local.set 0
    local.get 0
    return
  )
  (func $f257 (type 1)
    (local $l0 i32)
    (local $l1 i32)
    i32.const 0x00
    i32.const 0x00
    global.set 0
    global.set 1
    i32.const 0
    i32.const 9
    i32.store
    i32.const 512
    i32.const 0
    i32.store
    i32.const 256
    global.get 0
    i32.store
    i32.const 260
    global.get 1
    i32.store
    i32.const 100
    i64.extend_i32_u
    i32.const 0
    i32.const 512
    i32.const 256
    i32.const 8
    call $f3
    i32.const 768
    i32.const 0
    call $f29
    call $f30
    i32.const 768
    i32.load
    global.set 0
    global.set 1
    i32.const 0
    global.get 0
    global.get 1
    select
    global.set 0
    i32.const 1024
    global.get 0
    i32.store
    i32.const 1024
    i32.const 768
    call $f9
    i32.const 768
    i32.load
    local.set 1
    i32.const 0x0186a0
    local.get 1
    i32.sub
    local.set 0
    local.get 0
    return
  )
  (func $f258 (type 2)
    (local $l1 i32)
    (local $l2 i32)
    i32.const 0x00
    local.get 0
    global.set 0
    global.set 1
    i32.const 0
    i32.const 9
    i32.store
    i32.const 512
    i32.const 0
    i32.store
    i32.const 256
    global.get 0
    i32.store
    i32.const 260
    global.get 1
    i32.store
    i32.const 100
    i64.extend_i32_u
    i32.const 0
    i32.const 512
    i32.const 256
    i32.const 8
    call $f3
    i32.const 768
    i32.const 0
    call $f29
    call $f30
    i32.const 768
    i32.load
    global.set 0
    global.set 1
    i32.const 0
    global.get 0
    global.get 1
    select
    global.set 0
    i32.const 1024
    global.get 0
    i32.store
    i32.const 1024
    i32.const 768
    call $f9
    i32.const 768
    i32.load
    local.set 2
    local.get 2
    local.set 1
    local.get 1
    return
  )
  (func $f259 (type 3)
    (local $l2 i32)
    (local $l3 i32)
    (local $l4 i32)
    (local $l5 i32)
    i32.const 768
    call $f10
    i32.const 768
    i32.load
    local.set 3
    i32.const 0x00
    local.get 3
    global.set 0
    global.set 1
    i32.const 0
    i32.const 9
    i32.store
    i32.const 512
    i32.const 0
    i32.store
    i32.const 256
    global.get 0
    i32.store
    i32.const 260
    global.get 1
    i32.store
    i32.const 100
    i64.extend_i32_u
    i32.const 0
    i32.const 512
    i32.const 256
    i32.const 8
    call $f3
    i32.const 768
    i32.const 0
    call $f29
    call $f30
    i32.const 768
    i32.load
    global.set 0
    global.set 1
    i32.const 0
    global.get 0
    global.get 1
    select
    global.set 0
    i32.const 1024
    global.get 0
    i32.store
    i32.const 1024
    i32.const 768
    call $f9
    i32.const 768
    i32.load
    local.set 4
    i32.const 0x00
    local.get 0
    global.set 0
    global.set 1
    i32.const 0
    i32.const 9
    i32.store
    i32.const 512
    i32.const 0
    i32.store
    i32.const 256
    global.get 0
    i32.store
    i32.const 260
    global.get 1
    i32.store
    i32.const 100
    i64.extend_i32_u
    i32.const 0
    i32.const 512
    i32.const 256
    i32.const 8
    call $f3
    i32.const 768
    i32.const 0
    call $f29
    call $f30
    i32.const 768
    i32.load
    global.set 0
    global.set 1
    i32.const 0
    global.get 0
    global.get 1
    select
    global.set 0
    i32.const 1024
    global.get 0
    i32.store
    i32.const 1024
    i32.const 768
    call $f9
    i32.const 768
    i32.load
    local.set 5
    local.get 3
    local.get 0
    i32.ne
    local.get 4
    local.get 1
    i32.ge_u
    i32.and
    if 
      i32.const 0x00
      local.get 3
      global.set 0
      global.set 1
      i32.const 0
      i32.const 9
      i32.store
      i32.const 512
      i32.const 0
      i32.store
      i32.const 256
      global.get 0
      i32.store
      i32.const 260
      global.get 1
      i32.store
      i32.const 100
      i64.extend_i32_u
      i32.const 0
      i32.const 512
      i32.const 256
      i32.const 8
      call $f3
      i32.const 768
      i32.const 0
      call $f29
      call $f30
      i32.const 768
      i32.load
      global.set 0
      global.set 1
      i32.const 0
      global.get 0
      global.get 1
      select
      global.set 0
      i32.const 1024
      global.get 0
      i32.store
      local.get 4
      local.get 1
      i32.sub
      global.set 0
      i32.const 512
      global.get 0
      i32.store
      i32.const 1024
      i32.const 512
      call $f8
      i32.const 0x00
      local.get 0
      global.set 0
      global.set 1
      i32.const 0
      i32.const 9
      i32.store
      i32.const 512
      i32.const 0
      i32.store
      i32.const 256
      global.get 0
      i32.store
      i32.const 260
      global.get 1
      i32.store
      i32.const 100
      i64.extend_i32_u
      i32.const 0
      i32.const 512
      i32.const 256
      i32.const 8
      call $f3
      i32.const 768
      i32.const 0
      call $f29
      call $f30
      i32.const 768
      i32.load
      global.set 0
      global.set 1
      i32.const 0
      global.get 0
      global.get 1
      select
      global.set 0
      i32.const 1024
      global.get 0
      i32.store
      local.get 5
      local.get 1
      i32.add
      global.set 0
      i32.const 512
      global.get 0
      i32.store
      i32.const 1024
      i32.const 512
      call $f8
      i32.const 0x01
      local.set 2
    else 
      i32.const 0x00
      local.set 2
    end
    local.get 2
    return
  )
)
