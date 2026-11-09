module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.LocalComp.ExcO8W.Words
public meta import Certificates.Kernel.LocalComp.ExcO8W.Words
public meta import Certificates.Kernel.LocalComp.ExcO8W.ChainsData
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8WInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8WInputs
public import CFSG.Certificates.Kernel.SporSch.ChainKInvBase
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcO8W

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.Schreier CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ComponentClassification.RankTwoClassical.ExcO8W

@[expose] noncomputable def One240 : Nat := CFSG.KC.Enum.pidn 240 8

meta def unpk8 (x : Nat) : Array Nat := Array.ofFn (n := 240) fun i => (x >>> (8 * i.val)) % 256

meta def TG : Array (Array Nat) := (TGP.map unpk8).toArray

meta def STQ : Array (Array Nat) := (STQP.map unpk8).toArray

meta def G24 : Array (Array Nat) := (G24P.map unpk8).toArray

meta def G60 : Array (Array Nat) := (G60P.map unpk8).toArray

meta def G4 : Array (Array Nat) := (G4P.map unpk8).toArray

meta def G8 : Array (Array Nat) := (G8P.map unpk8).toArray

meta def S24 : Array (Array Nat) := (S24P.map unpk8).toArray

meta def S60 : Array (Array Nat) := (S60P.map unpk8).toArray

meta def S4 : Array (Array Nat) := (S4P.map unpk8).toArray

meta def S8 : Array (Array Nat) := (S8P.map unpk8).toArray

meta def RTL : List (Array Nat) := RTLP.map unpk8

meta def R24L : List (Array Nat) := R24LP.map unpk8

meta def R60L : List (Array Nat) := R60LP.map unpk8

meta def R4L : List (Array Nat) := R4LP.map unpk8

meta def R8L : List (Array Nat) := R8LP.map unpk8

meta def t24 : Array Nat := evalW 240 TG [3, 2, 1]

meta def t60 : Array Nat := evalW 240 TG [1]

meta def t4 : Array Nat := evalW 240 TG [5, 4, 3, 2, 1]

meta def t8 : Array Nat := evalW 240 TG [10, 8, 1]

meta def base7 : Array Nat := #[0, 1, 4, 8, 12, 16, 20]

meta def base5 : Array Nat := #[0, 1, 4, 12, 20]

meta def id240 : Array Nat := idA 240

meta def relab (bs : List Nat) : Array Nat := Id.run do
  let order := bs ++ (List.range 240).filter fun x => !bs.contains x
  let mut s := Array.replicate 240 0
  for i in [0:240] do
    s := s.set! order[i]! i
  return s

meta def sig7 : Array Nat := relab [0, 1, 4, 8, 12, 16, 20]

meta def sig5 : Array Nat := relab [0, 1, 4, 12, 20]

meta def cjA (s g : Array Nat) : Array Nat := comp s (comp g (invA s))

meta def CST : Array (Array Nat) := STQ.map (cjA sig7)

meta def CS24 : Array (Array Nat) := S24.map (cjA sig7)

meta def CS60 : Array (Array Nat) := S60.map (cjA sig7)

meta def CS4 : Array (Array Nat) := S4.map (cjA sig7)

meta def CS8 : Array (Array Nat) := S8.map (cjA sig5)

meta def sig7i : Array Nat := invA sig7

meta def sig5i : Array Nat := invA sig5

meta def baseC7 : Array Nat := #[0, 1, 2, 3, 4, 5, 6]

meta def baseC5 : Array Nat := #[0, 1, 2, 3, 4]

end CertificateChecks.KernelLC.ExcO8W

#ks_perm CertificateChecks.KernelLC.ExcO8W.X24 8 CertificateChecks.KernelLC.ExcO8W.t24
#ks_perm CertificateChecks.KernelLC.ExcO8W.X60 8 CertificateChecks.KernelLC.ExcO8W.t60
#ks_perm CertificateChecks.KernelLC.ExcO8W.X4 8 CertificateChecks.KernelLC.ExcO8W.t4
#ks_perm CertificateChecks.KernelLC.ExcO8W.X8 8 CertificateChecks.KernelLC.ExcO8W.t8

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.TQ 240 8 16 CertificateChecks.KernelLC.ExcO8W.STQ
  CertificateChecks.KernelLC.ExcO8W.base7 13 CertificateChecks.KernelLC.ExcO8W.tQWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.Q24 240 8 16 CertificateChecks.KernelLC.ExcO8W.S24
  CertificateChecks.KernelLC.ExcO8W.base7 9 CertificateChecks.KernelLC.ExcO8W.s24QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.Q60 240 8 16 CertificateChecks.KernelLC.ExcO8W.S60
  CertificateChecks.KernelLC.ExcO8W.base7 9 CertificateChecks.KernelLC.ExcO8W.s60QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.Q4 240 8 16 CertificateChecks.KernelLC.ExcO8W.S4
  CertificateChecks.KernelLC.ExcO8W.base7 8 CertificateChecks.KernelLC.ExcO8W.s4QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.Q8 240 8 16 CertificateChecks.KernelLC.ExcO8W.S8
  CertificateChecks.KernelLC.ExcO8W.base5 5 CertificateChecks.KernelLC.ExcO8W.s8QWords

#ks_perm CertificateChecks.KernelLC.ExcO8W.Sig7 8 CertificateChecks.KernelLC.ExcO8W.sig7
#ks_perm CertificateChecks.KernelLC.ExcO8W.Sig7I 8 CertificateChecks.KernelLC.ExcO8W.sig7i
#ks_perm CertificateChecks.KernelLC.ExcO8W.Sig5 8 CertificateChecks.KernelLC.ExcO8W.sig5
#ks_perm CertificateChecks.KernelLC.ExcO8W.Sig5I 8 CertificateChecks.KernelLC.ExcO8W.sig5i

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.CQT 240 8 16 CertificateChecks.KernelLC.ExcO8W.CST
  CertificateChecks.KernelLC.ExcO8W.baseC7 13 CertificateChecks.KernelLC.ExcO8W.tQWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.CQ24 240 8 16 CertificateChecks.KernelLC.ExcO8W.CS24
  CertificateChecks.KernelLC.ExcO8W.baseC7 9 CertificateChecks.KernelLC.ExcO8W.s24QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.CQ60 240 8 16 CertificateChecks.KernelLC.ExcO8W.CS60
  CertificateChecks.KernelLC.ExcO8W.baseC7 9 CertificateChecks.KernelLC.ExcO8W.s60QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.CQ4 240 8 16 CertificateChecks.KernelLC.ExcO8W.CS4
  CertificateChecks.KernelLC.ExcO8W.baseC7 8 CertificateChecks.KernelLC.ExcO8W.s4QWords

#ks_rawchain CertificateChecks.KernelLC.ExcO8W.CQ8 240 8 16 CertificateChecks.KernelLC.ExcO8W.CS8
  CertificateChecks.KernelLC.ExcO8W.baseC5 5 CertificateChecks.KernelLC.ExcO8W.s8QWords

namespace CertificateChecks.KernelLC.ExcO8W

open CFSG.KS CFSG.KS.SporSch.MOC CFSG.KC.ForallChunks

@[expose] def CNT.CS : List Nat :=
  [143, 144, 72, 40, 16, 72, 40, 16, 40, 16, 40, 16, 16, 16, 16, 16]

@[expose] noncomputable def CNT.K (k₀ : Nat) : Nat :=
  cntInvBK 240 8 (mask 8) (240 * 8) 7 CQT.LR CQT.TR k₀

theorem CNT.c0 : Nat.beq (CNT.K 0) 143 = true := by quickRfl
theorem CNT.c1 : Nat.beq (CNT.K 1) 144 = true := by quickRfl
theorem CNT.c2 : Nat.beq (CNT.K 2) 72 = true := by quickRfl
theorem CNT.c3 : Nat.beq (CNT.K 3) 40 = true := by quickRfl
theorem CNT.c4 : Nat.beq (CNT.K 4) 16 = true := by quickRfl
theorem CNT.c5 : Nat.beq (CNT.K 5) 72 = true := by quickRfl
theorem CNT.c6 : Nat.beq (CNT.K 6) 40 = true := by quickRfl
theorem CNT.c7 : Nat.beq (CNT.K 7) 16 = true := by quickRfl
theorem CNT.c8 : Nat.beq (CNT.K 8) 40 = true := by quickRfl
theorem CNT.c9 : Nat.beq (CNT.K 9) 16 = true := by quickRfl
theorem CNT.c10 : Nat.beq (CNT.K 10) 40 = true := by quickRfl
theorem CNT.c11 : Nat.beq (CNT.K 11) 16 = true := by quickRfl
theorem CNT.c12 : Nat.beq (CNT.K 12) 16 = true := by quickRfl
theorem CNT.c13 : Nat.beq (CNT.K 13) 16 = true := by quickRfl
theorem CNT.c14 : Nat.beq (CNT.K 14) 16 = true := by quickRfl
theorem CNT.c15 : Nat.beq (CNT.K 15) 16 = true := by quickRfl

theorem CNT.hc : ∀ k₀ < 16, CNT.K k₀ = CNT.CS.getD k₀ 0 :=
  forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
  (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
  (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ forall_lt_zero
  (Nat.eq_of_beq_eq_true CNT.c0 :)) (Nat.eq_of_beq_eq_true CNT.c1 :))
  (Nat.eq_of_beq_eq_true CNT.c2 :)) (Nat.eq_of_beq_eq_true CNT.c3 :))
  (Nat.eq_of_beq_eq_true CNT.c4 :)) (Nat.eq_of_beq_eq_true CNT.c5 :))
  (Nat.eq_of_beq_eq_true CNT.c6 :)) (Nat.eq_of_beq_eq_true CNT.c7 :))
  (Nat.eq_of_beq_eq_true CNT.c8 :)) (Nat.eq_of_beq_eq_true CNT.c9 :)) (Nat.eq_of_beq_eq_true CNT.c10 :)) (Nat.eq_of_beq_eq_true
  CNT.c11 :)) (Nat.eq_of_beq_eq_true CNT.c12 :)) (Nat.eq_of_beq_eq_true CNT.c13 :))
  (Nat.eq_of_beq_eq_true CNT.c14 :)) (Nat.eq_of_beq_eq_true CNT.c15 :)

@[expose] def CN24.CS : List Nat := [143, 72, 40, 40, 72, 40, 40, 144]

@[expose] noncomputable def CN24.K (k₀ : Nat) : Nat :=
  cntInvBK 240 8 (mask 8) (240 * 8) 7 CQ24.LR CQ24.TR k₀

theorem CN24.c0 : Nat.beq (CN24.K 0) 143 = true := by quickRfl
theorem CN24.c1 : Nat.beq (CN24.K 1) 72 = true := by quickRfl
theorem CN24.c2 : Nat.beq (CN24.K 2) 40 = true := by quickRfl
theorem CN24.c3 : Nat.beq (CN24.K 3) 40 = true := by quickRfl
theorem CN24.c4 : Nat.beq (CN24.K 4) 72 = true := by quickRfl
theorem CN24.c5 : Nat.beq (CN24.K 5) 40 = true := by quickRfl
theorem CN24.c6 : Nat.beq (CN24.K 6) 40 = true := by quickRfl
theorem CN24.c7 : Nat.beq (CN24.K 7) 144 = true := by quickRfl

theorem CN24.hc : ∀ k₀ < 8, CN24.K k₀ = CN24.CS.getD k₀ 0 :=
  forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
  (forall_lt_succ (forall_lt_succ forall_lt_zero (Nat.eq_of_beq_eq_true CN24.c0 :))
  (Nat.eq_of_beq_eq_true CN24.c1 :)) (Nat.eq_of_beq_eq_true CN24.c2 :)) (Nat.eq_of_beq_eq_true
  CN24.c3 :)) (Nat.eq_of_beq_eq_true CN24.c4 :)) (Nat.eq_of_beq_eq_true CN24.c5 :))
  (Nat.eq_of_beq_eq_true CN24.c6 :)) (Nat.eq_of_beq_eq_true CN24.c7 :)

@[expose] def CN60.CS : List Nat := [143, 72, 72, 144]

@[expose] noncomputable def CN60.K (k₀ : Nat) : Nat :=
  cntInvBK 240 8 (mask 8) (240 * 8) 7 CQ60.LR CQ60.TR k₀

theorem CN60.c0 : Nat.beq (CN60.K 0) 143 = true := by quickRfl
theorem CN60.c1 : Nat.beq (CN60.K 1) 72 = true := by quickRfl
theorem CN60.c2 : Nat.beq (CN60.K 2) 72 = true := by quickRfl
theorem CN60.c3 : Nat.beq (CN60.K 3) 144 = true := by quickRfl

theorem CN60.hc : ∀ k₀ < 4, CN60.K k₀ = CN60.CS.getD k₀ 0 :=
  forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ forall_lt_zero
  (Nat.eq_of_beq_eq_true CN60.c0 :)) (Nat.eq_of_beq_eq_true CN60.c1 :)) (Nat.eq_of_beq_eq_true
  CN60.c2 :)) (Nat.eq_of_beq_eq_true CN60.c3 :)

@[expose] def CN4.CS : List Nat := [111, 56, 24, 24, 56, 24, 24, 112]

@[expose] noncomputable def CN4.K (k₀ : Nat) : Nat :=
  cntInvBK 240 8 (mask 8) (240 * 8) 7 CQ4.LR CQ4.TR k₀

theorem CN4.c0 : Nat.beq (CN4.K 0) 111 = true := by quickRfl
theorem CN4.c1 : Nat.beq (CN4.K 1) 56 = true := by quickRfl
theorem CN4.c2 : Nat.beq (CN4.K 2) 24 = true := by quickRfl
theorem CN4.c3 : Nat.beq (CN4.K 3) 24 = true := by quickRfl
theorem CN4.c4 : Nat.beq (CN4.K 4) 56 = true := by quickRfl
theorem CN4.c5 : Nat.beq (CN4.K 5) 24 = true := by quickRfl
theorem CN4.c6 : Nat.beq (CN4.K 6) 24 = true := by quickRfl
theorem CN4.c7 : Nat.beq (CN4.K 7) 112 = true := by quickRfl

theorem CN4.hc : ∀ k₀ < 8, CN4.K k₀ = CN4.CS.getD k₀ 0 :=
  forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
  (forall_lt_succ (forall_lt_succ forall_lt_zero (Nat.eq_of_beq_eq_true CN4.c0 :))
  (Nat.eq_of_beq_eq_true CN4.c1 :)) (Nat.eq_of_beq_eq_true CN4.c2 :))
  (Nat.eq_of_beq_eq_true CN4.c3 :)) (Nat.eq_of_beq_eq_true CN4.c4 :))
  (Nat.eq_of_beq_eq_true CN4.c5 :)) (Nat.eq_of_beq_eq_true CN4.c6 :))
  (Nat.eq_of_beq_eq_true CN4.c7 :)

@[expose] def CN8.CS : List Nat := [79, 80, 8, 8, 8, 8, 24, 24]

@[expose] noncomputable def CN8.K (k₀ : Nat) : Nat :=
  cntInvBK 240 8 (mask 8) (240 * 8) 5 CQ8.LR CQ8.TR k₀

theorem CN8.c0 : Nat.beq (CN8.K 0) 79 = true := by quickRfl
theorem CN8.c1 : Nat.beq (CN8.K 1) 80 = true := by quickRfl
theorem CN8.c2 : Nat.beq (CN8.K 2) 8 = true := by quickRfl
theorem CN8.c3 : Nat.beq (CN8.K 3) 8 = true := by quickRfl
theorem CN8.c4 : Nat.beq (CN8.K 4) 8 = true := by quickRfl
theorem CN8.c5 : Nat.beq (CN8.K 5) 8 = true := by quickRfl
theorem CN8.c6 : Nat.beq (CN8.K 6) 24 = true := by quickRfl
theorem CN8.c7 : Nat.beq (CN8.K 7) 24 = true := by quickRfl

theorem CN8.hc : ∀ k₀ < 8, CN8.K k₀ = CN8.CS.getD k₀ 0 :=
  forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
  (forall_lt_succ (forall_lt_succ forall_lt_zero (Nat.eq_of_beq_eq_true CN8.c0 :))
  (Nat.eq_of_beq_eq_true CN8.c1 :)) (Nat.eq_of_beq_eq_true CN8.c2 :))
  (Nat.eq_of_beq_eq_true CN8.c3 :)) (Nat.eq_of_beq_eq_true CN8.c4 :))
  (Nat.eq_of_beq_eq_true CN8.c5 :)) (Nat.eq_of_beq_eq_true CN8.c6 :))
  (Nat.eq_of_beq_eq_true CN8.c7 :)

end CertificateChecks.KernelLC.ExcO8W

#lc_reps CertificateChecks.KernelLC.ExcO8W.RT 8 CertificateChecks.KernelLC.ExcO8W.TG
  CertificateChecks.KernelLC.ExcO8W.RTL

#lc_reps CertificateChecks.KernelLC.ExcO8W.R24 8 CertificateChecks.KernelLC.ExcO8W.G24
  CertificateChecks.KernelLC.ExcO8W.R24L

#lc_reps CertificateChecks.KernelLC.ExcO8W.R60 8 CertificateChecks.KernelLC.ExcO8W.G60
  CertificateChecks.KernelLC.ExcO8W.R60L

#lc_reps CertificateChecks.KernelLC.ExcO8W.R4 8 CertificateChecks.KernelLC.ExcO8W.G4
  CertificateChecks.KernelLC.ExcO8W.R4L

#lc_reps CertificateChecks.KernelLC.ExcO8W.R8 8 CertificateChecks.KernelLC.ExcO8W.G8
  CertificateChecks.KernelLC.ExcO8W.R8L

end
