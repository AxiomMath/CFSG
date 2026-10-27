module

public import Certificates.Kernel.Sporadic.Fi24Ext.Data

public section

namespace CFSG.KD.Fi24Ext

@[expose] noncomputable def c (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC g)
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE g)) (ST g)

@[expose] noncomputable def f (k : Nat) : Bool :=
  CFSG.KC.Fi24Ext.digRowsOK (Nat.land F CFSG.KD.BrFi24.LO) (Nat.shiftRight F 609961) CTF 0 781 false
    (196 * k) (Nat.min 196 (781 - 196 * k)) 4

end CFSG.KD.Fi24Ext

end
