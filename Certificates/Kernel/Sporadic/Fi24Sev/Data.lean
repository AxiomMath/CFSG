module

import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
public import Certificates.Kernel.Sporadic.Fi24Kit.Data
public import Certificates.Data.Kernel.Spor.Fi24Sev

#kc_repo #kc_json_gz CFSG.KD.Fi24Sev "Certificates/Kernel/Sporadic/Fi24Sev/data/f6.json.gz" 14003 1926778489746678549 (wrA : List Nat) (wsA : List (List Nat)) (omA : Nat) (cvA : Nat) (cwA : Nat) (szA : Nat) (repsA : List Nat) (rfA : List (List (Nat × Nat) × Nat × Nat × Nat)) (bpA : List (Nat × Nat)) (bposA : List Nat) (bwA : List Nat) (bsA : List Nat) (wrB : List Nat) (wsB : List (List Nat)) (omB : Nat) (cvB : Nat) (cwB : Nat) (szB : Nat) (repsB : List Nat) (rfB : List (List (Nat × Nat) × Nat × Nat × Nat)) (bpB : List (Nat × Nat)) (bposB : List Nat) (bwB : List Nat) (bsB : List Nat) (twB : List (Nat × List (List Nat))) (sl : List (Nat × List Nat × List Nat))

public section

namespace CFSG.KD.Fi24Sev

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

@[expose] noncomputable def OL : Nat → Nat := CFSG.KD.Fi24Orb.OL

@[expose] noncomputable def relA : Bool := relOK NW NT wrA wsA

@[expose] noncomputable def relB : Bool := relOK NW NT wrB wsB

@[expose] noncomputable def covA : Bool := covOK NW NT wsA cvA repsA cwA omA szA

@[expose] noncomputable def covB : Bool := covOK NW NT wsB cvB repsB cwB omB szB

@[expose] noncomputable def refA : Bool := refsOK NW NT OL wrA omA repsA rfA

@[expose] noncomputable def refB : Bool := refsOK NW NT OL wrB omB repsB rfB

@[expose] noncomputable def baseA : Bool := baseOK NW NT OL wrA omA bpA bposA bwA bsA

@[expose] noncomputable def baseB : Bool := baseOK NW NT OL wrB omB bpB bposB bwB bsB

@[expose] noncomputable def mv4 : Bool :=
  andB (notB (Nat.beq (letN NW (nat_lit 24) (nat_lit 4)) (nat_lit 4)))
    (notB (Nat.beq (letN NW (nat_lit 24) (letN NW (nat_lit 24) (nat_lit 4))) (nat_lit 4)))

@[expose] noncomputable def twin : Bool :=
  allL (fun t => twinOK NW NT OL wrB t.1 bpB bposB t.2) twB

@[expose] noncomputable def slc : Bool := slOK NW NT sl

end CFSG.KD.Fi24Sev

end
