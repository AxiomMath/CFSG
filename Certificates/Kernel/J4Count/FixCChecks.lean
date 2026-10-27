
module

public import Certificates.Data.Kernel.J4FixC
public import Certificates.Kernel.J4Count.FixCData
public import Certificates.Kernel.SporSch.J4S.NoCK
public import Certificates.Kernel.SporSch.J4S.XY
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixC

open CFSG.KC.Enum CFSG.KC.J4FixC CFSG.KC.J4Count CFSG.KD.J4FixC CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4NoCK CertificateChecks.KernelSporSch.J4Eta

@[expose] noncomputable def GN (l : Nat) : List (List Nat × Nat) := nth [] G l

@[expose] noncomputable def GP (l : Nat) : List Nat := (GN l).map (genP J4X J4XI J4Y J4YI)

@[expose] noncomputable def GIP (l : Nat) : List Nat := (GN l).map (genIP J4X J4XI J4Y J4YI)

@[expose] noncomputable def EV (l : Nat) (w : List Nat) : Nat := evalW (GP l) (GIP l) w

@[expose] noncomputable def PL (l : Nat) : List Nat := (nth [] PW l).map (EV l)

@[expose] noncomputable def RL (l : Nat) : List Nat := (nth [] RW l).map (EV l)

@[expose] noncomputable def FL (l : Nat) : List Nat := (nth [] FW l).map (EV l)

@[expose] noncomputable def CWL (l r : Nat) : List (List Nat) := nth [] (nth [] CW l) r

@[expose] noncomputable def CL (l r : Nat) : List Nat := (CWL l r).map (EV l)

@[expose] noncomputable def CIL (l r : Nat) : List Nat := (CWL l r).map fun w => EV l (invW w)

@[expose] noncomputable def TL (l r : Nat) : List Nat :=
  (nth [] (nth [] TW l) r).map (evalW (CL l r) (CIL l r))

@[expose] noncomputable def NR (l : Nat) : Nat := (nth [] RW l).length

theorem fix_ok : allN 7 (fun l =>
    fixAllK CFSG.KD.J4Q.rm (R 1) (R 10) (R 2) (R 11) etaK (J4RV l) (GN l)) = true := by quickRfl

theorem pdist_ok : allN 7 (fun l => distinctK (PL l)) = true := by quickRfl

theorem pclosed_ok : allN 7 (fun l => closedK (PL l)) = true := by quickRfl

theorem plen_ok : allN 7 (fun l => bAnd(Nat.beq (PL l).length (nth 0 NP l),
    bAnd(Nat.beq (FL l).length (nth 0 NP l), Nat.beq (nth [] PT l).length (nth 0 NP l)))) = true := by
  quickRfl

theorem tag_ok : allN 7 (fun l => allN (nth 0 NP l) fun i =>
    tagK (RL l) (nth 0 (PL l) i) (nth 0 (FL l) i) (nth 0 (nth [] PT l) i)) = true := by quickRfl

theorem comm_ok : allN 7 (fun l => allN (NR l) fun r => commK (nth 0 (RL l) r) (CL l r)) = true := by
  quickRfl

theorem sorted_ok : allN 7 (fun l => allN (NR l) fun r => sortedK (TL l r) 0) = true := by quickRfl

theorem tlen_ok : allN 7 (fun l => allN (NR l) fun r =>
    Nat.beq (TL l r).length (nth 0 (nth [] NT l) r)) = true := by quickRfl

theorem cnt_ok : allN 7 (fun l => allN (NR l) fun r =>
    Nat.beq (cntAK (nth [] BS l) (nth [] PS l) (pcK (nth 0 (RL l) r))) (nth 0 (nth [] NA l) r)) =
      true := by quickRfl

theorem neg_fix : notK (fixAllK CFSG.KD.J4Q.rm (R 1) (R 10) (R 2) (R 11) etaK (J4RV 3)
    [((nth ([], 0) (GN 3) 0).1, Nat.xor (nth ([], 0) (GN 3) 0).2 1)]) = true := by quickRfl

theorem neg_dist : notK (distinctK (nth 0 (PL 6) 1 :: PL 6)) = true := by quickRfl

theorem neg_closed : notK (closedK (PL 6).tail) = true := by quickRfl

theorem neg_tag : notK (allN (nth 0 NP 6) fun i =>
    tagK (RL 6) (nth 0 (PL 6) i) (nth 0 (FL 6) i) 0) = true := by quickRfl

theorem neg_sorted : notK (sortedK (nth 0 (TL 6 1) 1 :: nth 0 (TL 6 1) 0 :: (TL 6 1).drop 2) 0) =
    true := by quickRfl

theorem neg_comm : notK (allN 9 fun i => commK (nth 0 (PL 5) i) (CL 5 0)) = true := by quickRfl

theorem neg_cnt : notK (Nat.beq (cntAK (nth [] BS 5) (nth [] PS 5) (pcK (nth 0 (RL 5) 0))) 7) =
    true := by quickRfl

end CertificateChecks.KernelJ4Count.FixC

end
