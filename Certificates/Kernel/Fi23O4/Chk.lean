module

public import Certificates.Data.Kernel.B32
public import Certificates.Data.Kernel.Fi23O4
public import Certificates.Data.Kernel.Spor.TextAt
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24OrdersData
import CFSG.Certificates.Kernel.BabyMonster.Load
public import Mathlib

public section

set_option maxRecDepth 400000

#ks_chars CFSG.KD.Fi23O4.S CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi23FourSlp

namespace CFSG.KD.Fi23O4

open CFSG.KC.Enum CFSG.KC.B32 CFSG.KC.Fi23O4 CFSG.KD.Fi23K

@[expose] noncomputable def prog : List (Nat × Nat) := pairs S.chars

@[expose] def base : Array (List Nat) := #[[39], [40], [39], [41]]

@[expose] noncomputable def words : Array (List Nat) := slpWords base prog

@[expose] noncomputable def facts : Bool :=
  bAnd(CFSG.KS.Text.asciiK S.chars, bAnd(Nat.beq prog.length 176,
    fourK G words[18]! words[179]!))

end CFSG.KD.Fi23O4

#bm_bool CFSG.KD.Fi23O4 facts_ok (facts)
