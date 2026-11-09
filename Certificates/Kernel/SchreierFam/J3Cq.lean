module

public import Certificates.Kernel.Sporadic.J3K.Data
public import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Data.Kernel.SchreierFam.All3
public import Certificates.Data.Kernel.SchreierFam.CqK
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Spor.WordChunk
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Data
meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PinvSPcomp
import CFSG.Certificates.Kernel.Spor.RawOrbHead

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSchreierFam.J3Cq

open CFSG.ClassicalInvolution.J3Data CFSG.Monster.B.Co2.Native

meta def kRlM : Array (Int × Int) :=
  #[(1, 2), (-2, -1), (3, 3), (-2, 4), (3, 2), (5, 7), (6, 4), (9, 4), (6, 10), (8, 8), (4, 9),
    (13, 6), (6, 6), (11, 10), (14, 2), (12, 5), (5, 8), (15, 16), (17, 18), (19, 5), (20, 21),
    (23, 22), (11, 11), (14, -2), (12, 7), (12, 3), (25, 26), (27, 28), (29, 30)]

meta def kRlSM : Array (Int × Int) :=
  #[(-2, 1), (3, 1), (2, -1), (2, 1), (4, 3), (7, 4), (8, 1), (2, 5), (10, 6), (1, -2), (12, -2),
    (13, -1), (6, 1), (15, 5), (16, 3), (17, 2)]

meta def rvM (S SI : Array (Array Nat)) (rl : Array (Int × Int)) : Array (Array Nat) := Id.run do
  let mut v : Array (Array Nat) := Array.mkEmpty rl.size
  for (x, y) in rl do
    let f := fun (z : Int) =>
      if 3 ≤ z then v[(z - 3).toNat]! else if 0 < z then S[z.toNat - 1]! else SI[(-z).toNat - 1]!
    v := v.push (compA 20520 (f x) (f y))
  return v

meta def abTabM : Array (Array Nat) :=
  ((((include_str "../../Data/Kernel/SchreierFam/j3ab.txt" : String).splitOn "\n").filter
    (· ≠ "")).map fun l => ((l.splitOn " ").map String.toNat!).toArray).toArray

meta def abInvM : Array (Array Nat) := abTabM.map (invCand 20520)

meta def kRvM : Array (Array Nat) := rvM abTabM abInvM kRlM

meta def sRvM : Array (Array Nat) :=
  let k := kRvM
  rvM #[k[21]!, k[28]!] #[invCand 20520 k[21]!, invCand 20520 k[28]!] kRlSM

meta def sStrongM : Array (Array Nat) :=
  let s := sRvM
  #[s[6]!, s[8]!, s[11]!, s[15]!]

meta partial def packDC (a : Array Nat) (lo n : Nat) : Nat :=
  if n ≤ 1 then (if n = 1 then a[lo]! else 0)
  else packDC a lo (n / 2) ||| (packDC a (lo + n / 2) (n - n / 2) <<< (15 * (n / 2)))

meta def jj3M : Array Nat :=
  let kv := kRvM
  let k0 := kv[21]!
  let k1 := kv[28]!
  let ki0 := invCand 20520 k0
  let ki1 := invCand 20520 k1
  (#[abTabM[0]!, abTabM[1]!, abInvM[0]!, abInvM[1]!, k0, k1, ki0, ki1, compA 20520 k0 k0,
      compA 20520 ki0 ki0] ++ kv ++ rvM #[k0, k1] #[ki0, ki1] kRlSM).map
    fun t => packDC t 0 t.size

end CertificateChecks.KernelSchreierFam.J3Cq

#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.JJ3 307800
  CertificateChecks.KernelSchreierFam.J3Cq.jj3M

public section

namespace CertificateChecks.KernelSchreierFam.J3Cq

@[expose] def sD : List (List Int) := []

end CertificateChecks.KernelSchreierFam.J3Cq

#ks_rawchain_sl2_data CertificateChecks.KernelSchreierFam.J3Cq.SY 20520 15 0 16
  CertificateChecks.KernelSchreierFam.J3Cq.sStrongM CFSG.ClassicalInvolution.J3Data.sBase 4
  CertificateChecks.KernelSchreierFam.J3Cq.sD

namespace CertificateChecks.KernelSchreierFam.J3Cq

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KC.Misc.ArrEnum CFSG.KS.SchreierFam
  CFSG.KS.SporSch CertificateChecks.KernelSpor.J3K CFSG.ClassicalInvolution.J3Data

@[expose] noncomputable def jj3 (j : Nat) : Nat :=
  fld(JJ3, Nat.mul (nat_lit 307800) j, mask (nat_lit 307800))

@[expose] noncomputable def A : Nat := jj3 (nat_lit 0)
@[expose] noncomputable def B : Nat := jj3 (nat_lit 1)
@[expose] noncomputable def AI : Nat := jj3 (nat_lit 2)
@[expose] noncomputable def BI : Nat := jj3 (nat_lit 3)
@[expose] noncomputable def K0 : Nat := jj3 (nat_lit 4)
@[expose] noncomputable def K1 : Nat := jj3 (nat_lit 5)
@[expose] noncomputable def KI0 : Nat := jj3 (nat_lit 6)
@[expose] noncomputable def KI1 : Nat := jj3 (nat_lit 7)
@[expose] noncomputable def W1 : Nat := jj3 (nat_lit 8)
@[expose] noncomputable def W1I : Nat := jj3 (nat_lit 9)
@[expose] noncomputable def KRV (k : Nat) : Nat := jj3 (Nat.add (nat_lit 10) k)
@[expose] noncomputable def SRV (k : Nat) : Nat := jj3 (Nat.add (nat_lit 39) k)

@[expose] noncomputable def AB (h : Nat) : Nat := nIf(Nat.beq h (nat_lit 0), A, B)

@[expose] noncomputable def ABI (h : Nat) : Nat := nIf(Nat.beq h (nat_lit 0), AI, BI)

@[expose] noncomputable def KK (h : Nat) : Nat := nIf(Nat.beq h (nat_lit 0), K0, K1)

@[expose] noncomputable def KKI (h : Nat) : Nat := nIf(Nat.beq h (nat_lit 0), KI0, KI1)

@[expose] noncomputable def pmkHR (w : Nat) (rd : Nat → Nat → Nat) (p q : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun lo => rd p (rd q lo))
    (fun d ih lo => Nat.lor (ih lo)
      (Nat.shiftLeft (ih (Nat.add lo (Nat.shiftLeft (nat_lit 1) d)))
        (Nat.mul w (Nat.shiftLeft (nat_lit 1) d))))

@[expose] noncomputable def rdBlk (w p i : Nat) : Nat :=
  strictN (Nat.shiftRight i (nat_lit 10)) fun h =>
    fld(fld(p, Nat.mul (Nat.shiftLeft w (nat_lit 10)) h, mask (Nat.shiftLeft w (nat_lit 10))),
      Nat.mul w (Nat.land i (nat_lit 1023)), mask w)

@[expose] noncomputable def rdLeaf8 (w q lo : Nat) : Nat :=
  strictN (Nat.shiftRight lo (nat_lit 10)) fun h =>
    fld(fld(q, Nat.mul (Nat.shiftLeft w (nat_lit 10)) h, mask (Nat.mul w (nat_lit 1031))),
      Nat.mul w (Nat.land lo (nat_lit 1023)), mask (Nat.mul w (nat_lit 8)))

@[expose] noncomputable def pmkH8Q (w p q : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun lo => strictN (rdLeaf8 w q lo) fun Q => Nat.lor
      (Nat.lor
        (Nat.lor (rdBlk w p fld(Q, Nat.mul w (nat_lit 0), mask w))
          (Nat.shiftLeft (rdBlk w p fld(Q, Nat.mul w (nat_lit 1), mask w)) w))
        (Nat.shiftLeft
          (Nat.lor (rdBlk w p fld(Q, Nat.mul w (nat_lit 2), mask w))
            (Nat.shiftLeft (rdBlk w p fld(Q, Nat.mul w (nat_lit 3), mask w)) w))
          (Nat.mul w (nat_lit 2))))
      (Nat.shiftLeft
        (Nat.lor
          (Nat.lor (rdBlk w p fld(Q, Nat.mul w (nat_lit 4), mask w))
            (Nat.shiftLeft (rdBlk w p fld(Q, Nat.mul w (nat_lit 5), mask w)) w))
          (Nat.shiftLeft
            (Nat.lor (rdBlk w p fld(Q, Nat.mul w (nat_lit 6), mask w))
              (Nat.shiftLeft (rdBlk w p fld(Q, Nat.mul w (nat_lit 7), mask w)) w))
            (Nat.mul w (nat_lit 2))))
        (Nat.mul w (nat_lit 4))))
    (fun d ih lo => Nat.lor (ih lo)
      (Nat.shiftLeft (ih (Nat.add lo (Nat.shiftLeft (nat_lit 8) d)))
        (Nat.mul w (Nat.shiftLeft (nat_lit 8) d))))

@[expose] noncomputable def pcompG (n w : Nat) (H H8 : Nat → Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih b rem => nIf(Nat.beq rem (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0),
        ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)),
        strictN (Nat.sub n (Nat.shiftLeft rem b)) (fun lo =>
          Nat.lor (Nat.shiftLeft (nIf(Nat.blt b (nat_lit 3), H b lo,
              H8 (Nat.sub b (nat_lit 3)) lo)) (Nat.mul w lo))
            (ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)))))))
    (nat_lit 32) (nat_lit 0) n

@[expose] noncomputable def pcompB (n w p q : Nat) : Nat :=
  pcompG n w (pmkHR w (rdBlk w) p q) (pmkH8Q w p q)

theorem fld_fldJ (p a b w L : Nat) (h : b + w ≤ L) :
    ((p >>> a) &&& (2 ^ L - 1)) >>> b &&& (2 ^ w - 1) = (p >>> (a + b)) &&& (2 ^ w - 1) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hk : k < w
  · have hL : b + k < L := by omega
    simp [hk, hL, Nat.add_assoc]
  · simp [hk]

theorem rdBlk_eq (w p i : Nat) : rdBlk w p i = fld(p, Nat.mul w i, mask w) := by
  unfold rdBlk
  rw [CFSG.KS.PackFld.strictN_eqP]
  simp only [CFSG.KS.PackFld.mask_eq]
  have e1 : Nat.land i (nat_lit 1023) = i % 2 ^ 10 := Nat.and_two_pow_sub_one_eq_mod i 10
  have e2 : Nat.shiftRight i (nat_lit 10) = i / 2 ^ 10 := Nat.shiftRight_eq_div_pow i 10
  have e3 : Nat.shiftLeft w (nat_lit 10) = w * 2 ^ 10 := Nat.shiftLeft_eq w 10
  rw [e1, e2, e3]
  have hb : w * (i % 2 ^ 10) + w ≤ w * 2 ^ 10 := by
    have := Nat.mul_le_mul_left w (Nat.mod_lt i (Nat.two_pow_pos 10))
    rw [Nat.mul_succ] at this
    exact this
  change ((p >>> (w * 2 ^ 10 * (i / 2 ^ 10))) &&& (2 ^ (w * 2 ^ 10) - 1)) >>> (w * (i % 2 ^ 10))
      &&& (2 ^ w - 1) = (p >>> (w * i)) &&& (2 ^ w - 1)
  rw [fld_fldJ _ _ _ _ _ hb, Nat.mul_assoc, ← Nat.mul_add, Nat.div_add_mod]

theorem rdLeaf8_eq (w q lo k : Nat) (hk : k < 8) :
    fld(rdLeaf8 w q lo, Nat.mul w k, mask w) = fld(q, Nat.mul w (Nat.add lo k), mask w) := by
  unfold rdLeaf8
  rw [CFSG.KS.PackFld.strictN_eqP]
  simp only [CFSG.KS.PackFld.mask_eq]
  have e1 : Nat.land lo (nat_lit 1023) = lo % 2 ^ 10 := Nat.and_two_pow_sub_one_eq_mod lo 10
  have e2 : Nat.shiftRight lo (nat_lit 10) = lo / 2 ^ 10 := Nat.shiftRight_eq_div_pow lo 10
  have e3 : Nat.shiftLeft w (nat_lit 10) = w * 2 ^ 10 := Nat.shiftLeft_eq w 10
  rw [e1, e2, e3]
  have hm := Nat.mod_lt lo (Nat.two_pow_pos 10)
  have h1 : w * k + w ≤ w * 8 := by
    have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hk)
    rw [Nat.mul_succ] at this
    exact this
  have h2 : w * (lo % 2 ^ 10) + w * k + w ≤ w * 1031 := by
    have h3 : lo % 2 ^ 10 + k + 1 ≤ 1031 := by omega
    have := Nat.mul_le_mul_left w h3
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at this
    exact this
  change (((q >>> (w * 2 ^ 10 * (lo / 2 ^ 10))) &&& (2 ^ (w * 1031) - 1)) >>> (w * (lo % 2 ^ 10))
      &&& (2 ^ (w * 8) - 1)) >>> (w * k) &&& (2 ^ w - 1) = (q >>> (w * (lo + k))) &&& (2 ^ w - 1)
  rw [fld_fldJ _ _ _ _ _ h1, fld_fldJ _ _ _ _ _ (by omega), ← Nat.add_assoc, Nat.mul_assoc,
    ← Nat.mul_add, Nat.div_add_mod, ← Nat.mul_add]

theorem pmkHR_eq (w p q : Nat) : pmkHR w (rdBlk w) p q = pmkH w (mask w) p q := by
  unfold pmkHR pmkH
  simp only [rdBlk_eq]

theorem pmkH8Q_eq (w p q : Nat) : pmkH8Q w p q = pmkH8 w (mask w) p q := by
  funext d
  induction d with
  | zero =>
    funext lo
    have e : pmkH8Q w p q 0 lo = strictN (rdLeaf8 w q lo) fun Q => Nat.lor
      (Nat.lor
        (Nat.lor (rdBlk w p fld(Q, Nat.mul w (nat_lit 0), mask w))
          (Nat.shiftLeft (rdBlk w p fld(Q, Nat.mul w (nat_lit 1), mask w)) w))
        (Nat.shiftLeft
          (Nat.lor (rdBlk w p fld(Q, Nat.mul w (nat_lit 2), mask w))
            (Nat.shiftLeft (rdBlk w p fld(Q, Nat.mul w (nat_lit 3), mask w)) w))
          (Nat.mul w (nat_lit 2))))
      (Nat.shiftLeft
        (Nat.lor
          (Nat.lor (rdBlk w p fld(Q, Nat.mul w (nat_lit 4), mask w))
            (Nat.shiftLeft (rdBlk w p fld(Q, Nat.mul w (nat_lit 5), mask w)) w))
          (Nat.shiftLeft
            (Nat.lor (rdBlk w p fld(Q, Nat.mul w (nat_lit 6), mask w))
              (Nat.shiftLeft (rdBlk w p fld(Q, Nat.mul w (nat_lit 7), mask w)) w))
            (Nat.mul w (nat_lit 2))))
        (Nat.mul w (nat_lit 4))) := rfl
    rw [e, CFSG.KS.PackFld.strictN_eqP, rdLeaf8_eq w q lo (nat_lit 0) (by decide),
      rdLeaf8_eq w q lo (nat_lit 1) (by decide), rdLeaf8_eq w q lo (nat_lit 2) (by decide),
      rdLeaf8_eq w q lo (nat_lit 3) (by decide), rdLeaf8_eq w q lo (nat_lit 4) (by decide),
      rdLeaf8_eq w q lo (nat_lit 5) (by decide), rdLeaf8_eq w q lo (nat_lit 6) (by decide),
      rdLeaf8_eq w q lo (nat_lit 7) (by decide)]
    simp only [rdBlk_eq]
    rfl
  | succ d ih =>
    funext lo
    have e : ∀ H : Nat → Nat → Nat, H = pmkH8Q w p q → H (d + 1) lo = Nat.lor (H d lo)
        (Nat.shiftLeft (H d (Nat.add lo (Nat.shiftLeft (nat_lit 8) d)))
          (Nat.mul w (Nat.shiftLeft (nat_lit 8) d))) := by
      rintro H rfl
      rfl
    rw [e _ rfl, ih]
    rfl

theorem pcompB_eq (n w : Nat) : pcompB n w = pcomp n w (mask w) := by
  funext p q
  unfold pcompB
  rw [pmkHR_eq, pmkH8Q_eq]
  rfl

@[expose] noncomputable def canonKB (n w nw p : Nat) : Bool :=
  bAnd(szOK n w, bAnd(Nat.beq (Nat.shiftRight p nw) (nat_lit 0),
    allN n (fun i => Nat.blt (rdBlk w p i) n)))

theorem canonKB_eq (n w nw p : Nat) :
    canonKB n w nw p = CFSG.KS.Prim.canonK n w (mask w) nw p := by
  unfold canonKB CFSG.KS.Prim.canonK
  simp only [rdBlk_eq]
  rfl

@[expose] noncomputable def letVJ (S SI : Nat → Nat) (z : Int) : Nat :=
  strictN (CFSG.KS.Mathieu.icode z) fun c => nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
    S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def symVG (S SI RV : Nat → Nat) (z : Int) : Nat :=
  if 3 ≤ z then RV (z - 3).toNat else letVJ S SI z

@[expose] def exG (rl : List (Int × Int)) : Nat → Int → List Int
  | 0, z => [z]
  | f + 1, z => if 3 ≤ z then exG rl f (rl.getD (z - 3).toNat (0, 0)).1 ++
      exG rl f (rl.getD (z - 3).toNat (0, 0)).2 else [z]

@[expose] noncomputable def ruleG (n w : Nat) (S SI RV : Nat → Nat) (rl : List (Int × Int))
    (k : Nat) : Bool :=
  Nat.beq (RV k) (pcompB n w (symVG S SI RV (rl.getD k (0, 0)).1)
    (symVG S SI RV (rl.getD k (0, 0)).2))

def PermJ3 (n w T : Nat) : Prop := T >>> (n * w) = 0 ∧ ∀ i < n, pg w (mask w) T i < n

theorem PermJ3_of_canon {n w T : Nat} (h : CFSG.KS.Prim.canonK n w (mask w) (n * w) T = true) :
    PermJ3 n w T :=
  ⟨(CFSG.KS.PF.canon_facts h).2.2.1, (CFSG.KS.PF.canon_facts h).2.2.2⟩

theorem PermJ3_pcomp {n w p q : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) (hp : PermJ3 n w p)
    (hq : PermJ3 n w q) : PermJ3 n w (pcomp n w (mask w) p q) :=
  ⟨CFSG.KS.PF.pcomp_shr p q hn hw, fun i hi => by
    rw [CFSG.KS.PF.pg_pcomp hn hi]
    exact hp.2 _ (hq.2 i hi)⟩

theorem pcomp_assocJ3 {n w p q r : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) (hr : PermJ3 n w r) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r =
      pcomp n w (mask w) p (pcomp n w (mask w) q r) :=
  CFSG.KS.PF.eq_of_fields hw (CFSG.KS.PF.pcomp_shr _ _ hn hw) (CFSG.KS.PF.pcomp_shr _ _ hn hw)
    fun i hi => by
      rw [CFSG.KS.PF.pg_pcomp hn hi, CFSG.KS.PF.pg_pcomp hn (hr.2 i hi),
        CFSG.KS.PF.pg_pcomp hn hi, CFSG.KS.PF.pg_pcomp hn hi]

theorem wordAccK_consJ (n w m acc : Nat) (S SI : Nat → Nat) (z : Int) (l : List Int) :
    wordAccK n w m acc S SI (z :: l) = pcomp n w m (letVJ S SI z) (wordAccK n w m acc S SI l) := by
  have e : wordAccK n w m acc S SI (z :: l) =
      strictN (wordAccK n w m acc S SI l) (fun T => strictN (CFSG.KS.Mathieu.icode z) (fun c =>
        pcomp n w m (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
          S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
          SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T)) := rfl
  rw [e]
  unfold letVJ
  simp only [CFSG.KS.PackFld.strictN_eqP]

theorem wordAccK_appJ (n w m acc : Nat) (S SI : Nat → Nat) (a b : List Int) :
    wordAccK n w m acc S SI (a ++ b) = wordAccK n w m (wordAccK n w m acc S SI b) S SI a := by
  induction a with
  | nil => rfl
  | cons z a ih => rw [List.cons_append, wordAccK_consJ, wordAccK_consJ, ih]

theorem PermJ3_letVJ {n w : Nat} {S SI : Nat → Nat} (hS : ∀ h, PermJ3 n w (S h))
    (hSI : ∀ h, PermJ3 n w (SI h)) (z : Int) : PermJ3 n w (letVJ S SI z) := by
  unfold letVJ
  rw [CFSG.KS.PackFld.strictN_eqP]
  generalize Nat.beq (Nat.land (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 0) = b
  cases b with
  | false => exact hSI _
  | true => exact hS _

theorem exG_val {n w : Nat} {S SI RV : Nat → Nat} {rl : List (Int × Int)} (hn : n < 2 ^ 32)
    (hw : 0 < w) (hS : ∀ h, PermJ3 n w (S h)) (hSI : ∀ h, PermJ3 n w (SI h))
    (hord : ∀ k < rl.length,
      ((rl.getD k (0, 0)).1 < 3 ∨ ((rl.getD k (0, 0)).1 - 3).toNat < k) ∧
      ((rl.getD k (0, 0)).2 < 3 ∨ ((rl.getD k (0, 0)).2 - 3).toNat < k))
    (hR : ∀ k < rl.length, ruleG n w S SI RV rl k = true) :
    ∀ (f : Nat) (z : Int), (z < 3 ∨ ((z - 3).toNat < f ∧ (z - 3).toNat < rl.length)) →
      PermJ3 n w (symVG S SI RV z) ∧ ∀ T, PermJ3 n w T →
        wordAccK n w (mask w) T S SI (exG rl f z) = pcomp n w (mask w) (symVG S SI RV z) T := by
  have hlet : ∀ (f : Nat) (z : Int), ¬ 3 ≤ z → PermJ3 n w (symVG S SI RV z) ∧ ∀ T, PermJ3 n w T →
      wordAccK n w (mask w) T S SI (exG rl f z) = pcomp n w (mask w) (symVG S SI RV z) T := by
    intro f z h3
    have e : symVG S SI RV z = letVJ S SI z := by
      simp only [symVG, h3, ↓reduceIte]
    have ex : exG rl f z = [z] := by
      cases f with
      | zero => rfl
      | succ f => simp only [exG, h3, ↓reduceIte]
    refine ⟨by rw [e]; exact PermJ3_letVJ hS hSI z, fun T _ => ?_⟩
    rw [e, ex, wordAccK_consJ]
    rfl
  intro f
  induction f with
  | zero =>
    intro z hz
    exact hlet 0 z (by omega)
  | succ f ih =>
    intro z hz
    by_cases h3 : 3 ≤ z
    · have hk : (z - 3).toNat < f + 1 ∧ (z - 3).toNat < rl.length := by omega
      obtain ⟨hx, hy⟩ := hord _ hk.2
      have ihx := ih (rl.getD (z - 3).toNat (0, 0)).1 (by omega)
      have ihy := ih (rl.getD (z - 3).toNat (0, 0)).2 (by omega)
      have hr := hR _ hk.2
      unfold ruleG at hr
      rw [pcompB_eq] at hr
      have ev : symVG S SI RV z = RV (z - 3).toNat := by
        simp only [symVG, h3, ↓reduceIte]
      rw [ev, Nat.eq_of_beq_eq_true hr]
      have ex : exG rl (f + 1) z = exG rl f (rl.getD (z - 3).toNat (0, 0)).1 ++
          exG rl f (rl.getD (z - 3).toNat (0, 0)).2 := by
        simp only [exG, h3, ↓reduceIte]
      refine ⟨PermJ3_pcomp hn hw ihx.1 ihy.1, fun T hT => ?_⟩
      rw [ex, wordAccK_appJ, ihy.2 T hT, ihx.2 _ (PermJ3_pcomp hn hw ihy.1 hT),
        pcomp_assocJ3 hn hw hT]
    · exact hlet (f + 1) z h3

@[expose] def cqWords : List (List Nat) := [[0], [0, 0]]

@[expose] noncomputable def cqSl (L : List (List Nat)) (a : Nat) : Bool :=
  allN (rcnt (SY.LR 1)) fun b => allN (rcnt (SY.LR 2)) fun c =>
    cqK 20520 15 A KK L (pcomp 20520 15 (mask 15)
      (pcomp 20520 15 (mask 15) (trAt 20520 (20520 * 15) SY.LR SY.TR 0 a)
        (trAt 20520 (20520 * 15) SY.LR SY.TR 1 b))
      (trAt 20520 (20520 * 15) SY.LR SY.TR 2 c))

@[expose] noncomputable def cqS (a : Nat) : Bool := cqSl cqWords a

@[expose] noncomputable def cqC3 (w t0 t1 t2 x : Nat) : Nat :=
  pg w (mask w) t0 (pg w (mask w) t1 (pg w (mask w) t2 x))

@[expose] noncomputable def sqNe (n w R t0 t1 t2 x : Nat) : Bool :=
  bAnd(Nat.blt x n, bAnd(Nat.blt (pg w (mask w) t2 x) n, bAnd(Nat.blt (cqC3 w t0 t1 t2 x) n,
    bAnd(Nat.blt (pg w (mask w) t2 (cqC3 w t0 t1 t2 x)) n,
      bIf(Nat.beq (cqC3 w t0 t1 t2 (cqC3 w t0 t1 t2 x)) (pg w (mask w) R x), false, true)))))

@[expose] noncomputable def cqKP (n w R : Nat) (WS : List (Nat × Nat)) (x t0 t1 t2 : Nat) : Bool :=
  bIf(sqNe n w R t0 t1 t2 x, true,
    strictB (pcomp n w (mask w) (pcomp n w (mask w) t0 t1) t2) fun C =>
      WS.any fun p => invoNe n w R (pcomp n w (mask w) C
        (pcomp n w (mask w) p.1 (pcomp n w (mask w) C p.2))))

@[expose] noncomputable def invoNeI (n w R I X : Nat) : Bool :=
  bAnd(Nat.beq (pcompB n w X X) I, bIf(Nat.beq X I, false, bIf(Nat.beq X R, false, true)))

@[expose] noncomputable def cqKQ (n w R : Nat) (WS : List (Nat × Nat)) (x t0 t1 t2 : Nat) : Bool :=
  bIf(sqNe n w R t0 t1 t2 x, true,
    WS.any fun p => invoNeI n w R t1 (pcompB n w t0 (pcompB n w p.1 (pcompB n w t0 p.2))))

theorem pcomp_pidnJ {n w p : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hp : p >>> (n * w) = 0) : pcomp n w (mask w) p (pidn n w) = p := by
  have hn32 : n < 2 ^ 32 := lt_trans hn (by norm_num)
  exact CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw)
    (CFSG.KS.PF.pcomp_shr p _ hn32 (CFSG.KS.PF.w_pos hw)) hp fun i hi => by
      rw [CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pidn hn hw hi]

theorem cqKQ_eq {n w R : Nat} {WS : List (Nat × Nat)} {x t0 t1 t2 : Nat} (hn : n < 16777216)
    (hw : n + 1 < 2 ^ w) (h1 : t1 = pidn n w) (h2 : t2 = pidn n w)
    (h0 : Nat.shiftRight t0 (Nat.mul n w) = 0) :
    cqKQ n w R WS x t0 t1 t2 = cqKP n w R WS x t0 t1 t2 := by
  unfold cqKQ cqKP invoNeI invoNe
  rw [pcompB_eq, h1, h2, pcomp_pidnJ hn hw h0, pcomp_pidnJ hn hw h0, CFSG.KS.PackFld.strictB_eqP]

@[expose] noncomputable def cqWS : List (Nat × Nat) := [(K0, KI0), (W1, W1I)]

@[expose] def cqSel : Nat := 255211775190704452650736626023677297768

@[expose] noncomputable def cqWSel (a : Nat) : List (Nat × Nat) :=
  Bool.rec (motive := fun _ => List (Nat × Nat)) [(K0, KI0)] [(W1, W1I)]
    (Nat.beq (Nat.land (Nat.shiftRight cqSel a) (nat_lit 1)) (nat_lit 1))

theorem cqWSel_sub (a : Nat) : ∀ p ∈ cqWSel a, p ∈ cqWS := by
  intro p
  unfold cqWSel cqWS
  cases Nat.beq (Nat.land (Nat.shiftRight cqSel a) (nat_lit 1)) (nat_lit 1) with
  | false => exact fun hp => List.mem_cons.2 (Or.inl (List.mem_singleton.1 hp))
  | true =>
    exact fun hp => List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl (List.mem_singleton.1 hp))))

@[expose] noncomputable def cqTG (n w R : Nat) (WS : List (Nat × Nat)) (T : Nat → Nat → Nat)
    (a : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight (T 0 a) (Nat.mul n w)) (nat_lit 0),
    cqKQ n w R WS 0 (T 0 a) (T 1 0) (T 2 0))

@[expose] noncomputable def cqT (a : Nat) : Bool :=
  cqTG 20520 15 A (cqWSel a) (trAt 20520 (20520 * 15) SY.LR SY.TR) a

theorem strictB_eqJ (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bAnd_tJ {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a with
  | false => exact absurd h Bool.false_ne_true
  | true => exact ⟨rfl, h⟩

theorem bIf_fJ {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c with
  | false => rfl
  | true => exact absurd h Bool.false_ne_true

theorem cqC3_eq {n w t0 t1 t2 x : Nat} (hn : n < 2 ^ 32) (hx : x < n)
    (h2 : pg w (mask w) t2 x < n) :
    pg w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) t0 t1) t2) x = cqC3 w t0 t1 t2 x := by
  rw [CFSG.KS.PackFld.pg_pcomp hn hx, CFSG.KS.PackFld.pg_pcomp hn h2]
  rfl

theorem cqK_of_cqKP {n w R : Nat} {G : Nat → Nat} {L : List (List Nat)} {WS : List (Nat × Nat)}
    {x t0 t1 t2 : Nat} (hn : n < 2 ^ 32)
    (hWS : ∀ p ∈ WS, ∃ l ∈ L, wordK n w G l = p.1 ∧ pinvS n w (mask w) p.1 = p.2)
    (h : cqKP n w R WS x t0 t1 t2 = true) :
    cqK n w R G L (pcomp n w (mask w) (pcomp n w (mask w) t0 t1) t2) = true := by
  unfold cqKP at h
  unfold cqK
  cases hs : sqNe n w R t0 t1 t2 x with
  | false =>
    rw [hs, strictB_eqJ] at h
    obtain ⟨p, hp, hX⟩ := List.any_eq_true.1 h
    obtain ⟨l, hl, hW, hWI⟩ := hWS p hp
    generalize pcomp n w (mask w) (pcomp n w (mask w) t0 t1) t2 = C at hX ⊢
    cases Nat.beq (pcomp n w (mask w) C C) R with
    | false => rfl
    | true =>
      refine List.any_eq_true.2 ⟨l, hl, ?_⟩
      unfold cjK
      rw [hW, hWI]
      exact hX
  | true =>
    unfold sqNe at hs
    obtain ⟨hx, hs⟩ := bAnd_tJ hs
    obtain ⟨h2, hs⟩ := bAnd_tJ hs
    obtain ⟨h3, hs⟩ := bAnd_tJ hs
    obtain ⟨h4, hs⟩ := bAnd_tJ hs
    have hx := Nat.blt_eq.mp hx
    have h2 := Nat.blt_eq.mp h2
    have h3 := Nat.blt_eq.mp h3
    have h4 := Nat.blt_eq.mp h4
    have hne := Nat.ne_of_beq_eq_false (bIf_fJ hs)
    have hC : pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) t0 t1) t2)
        (pcomp n w (mask w) (pcomp n w (mask w) t0 t1) t2) ≠ R := by
      intro e
      apply hne
      rw [← e, CFSG.KS.PackFld.pg_pcomp hn hx, cqC3_eq hn hx h2, cqC3_eq hn h3 h4]
    cases hb : Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) t0 t1) t2)
        (pcomp n w (mask w) (pcomp n w (mask w) t0 t1) t2)) R with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb) hC

theorem a_pmk : Nat.beq A (pmk 20520 15 (r32 TA)) = true := by quickRfl

theorem b_pmk : Nat.beq B (pmk 20520 15 (r32 TB)) = true := by quickRfl

theorem cnAJ : CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) A = true := by
  rw [← canonKB_eq]
  quickRfl

theorem cnAI : CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) AI = true := by
  rw [← canonKB_eq]
  quickRfl

theorem cnBJ : CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) B = true := by
  rw [← canonKB_eq]
  quickRfl

theorem cnBI : CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) BI = true := by
  rw [← canonKB_eq]
  quickRfl

theorem pcAJ : pcomp 20520 15 (mask 15) A AI = pidn 20520 15 := by
  rw [← pcompB_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pcBJ : pcomp 20520 15 (mask 15) B BI = pidn 20520 15 := by
  rw [← pcompB_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem a_perm : permB 20520 15 A = true :=
  CFSG.KS.PinvS.permOK_pinvS cnAJ (CFSG.KS.PinvS.inv_of_pcomp cnAJ cnAI pcAJ).1

theorem b_perm : permB 20520 15 B = true :=
  CFSG.KS.PinvS.permOK_pinvS cnBJ (CFSG.KS.PinvS.inv_of_pcomp cnBJ cnBI pcBJ).1

theorem ai_eq : Nat.beq AI (pinvS 20520 15 (mask 15) A) = true := by
  rw [CFSG.KS.PinvS.pinvS_of_pcomp cnAJ cnAI pcAJ]
  exact Nat.beq_refl AI

theorem bi_eq : Nat.beq BI (pinvS 20520 15 (mask 15) B) = true := by
  rw [CFSG.KS.PinvS.pinvS_of_pcomp cnBJ cnBI pcBJ]
  exact Nat.beq_refl BI

@[expose] def rlJ : List (Int × Int) :=
  [(1, 2), (-2, -1), (3, 3), (-2, 4), (3, 2), (5, 7), (6, 4), (9, 4), (6, 10), (8, 8), (4, 9),
    (13, 6), (6, 6), (11, 10), (14, 2), (12, 5), (5, 8), (15, 16), (17, 18), (19, 5), (20, 21),
    (23, 22), (11, 11), (14, -2), (12, 7), (12, 3), (25, 26), (27, 28), (29, 30)]

@[expose] noncomputable def kRuleJ (k : Nat) : Bool := ruleG 20520 15 AB ABI KRV rlJ k

end CertificateChecks.KernelSchreierFam.J3Cq

#kon_slices CertificateChecks.KernelSchreierFam.J3Cq.kRuleJ 0 29
#kon_join CertificateChecks.KernelSchreierFam.J3Cq.kRuleJAll
  CertificateChecks.KernelSchreierFam.J3Cq.kRuleJ 29

namespace CertificateChecks.KernelSchreierFam.J3Cq

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SchreierFam CFSG.KS.SporSch
  CFSG.ClassicalInvolution.J3Data

theorem rlJ_ord : ∀ k < rlJ.length,
    ((rlJ.getD k (0, 0)).1 < 3 ∨ ((rlJ.getD k (0, 0)).1 - 3).toNat < k) ∧
    ((rlJ.getD k (0, 0)).2 < 3 ∨ ((rlJ.getD k (0, 0)).2 - 3).toNat < k) := by
  decide +kernel

theorem cnPid : CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) (pidn 20520 15) = true := by
  rw [← canonKB_eq]
  quickRfl

theorem PermJ3_AB : ∀ h, PermJ3 20520 15 (AB h) := fun h => by
  unfold AB
  generalize Nat.beq h (nat_lit 0) = b
  cases b with
  | false => exact PermJ3_of_canon cnBJ
  | true => exact PermJ3_of_canon cnAJ

theorem PermJ3_ABI : ∀ h, PermJ3 20520 15 (ABI h) := fun h => by
  unfold ABI
  generalize Nat.beq h (nat_lit 0) = b
  cases b with
  | false => exact PermJ3_of_canon cnBI
  | true => exact PermJ3_of_canon cnAI

theorem slp_val : ∀ (f : Nat) (z : Int), (z < 3 ∨ ((z - 3).toNat < f ∧ (z - 3).toNat < rlJ.length)) →
    PermJ3 20520 15 (symVG AB ABI KRV z) ∧ ∀ T, PermJ3 20520 15 T →
      wordAccK 20520 15 (mask 15) T AB ABI (exG rlJ f z) =
        pcomp 20520 15 (mask 15) (symVG AB ABI KRV z) T :=
  exG_val (by norm_num) (by norm_num) PermJ3_AB PermJ3_ABI rlJ_ord fun k hk => kRuleJAll k hk

theorem rv21 : Nat.beq (KRV 21) K0 = true := by quickRfl

theorem rv28 : Nat.beq (KRV 28) K1 = true := by quickRfl

theorem k0_wordJ : wordK 20520 15 (mask 15) (pidn 20520 15) AB ABI kWordsAB[0]! = K0 := by
  have ew : kWordsAB[0]! = exG rlJ 29 24 := by decide +kernel
  have hv := slp_val 29 24 (by decide +kernel)
  have e24 : symVG AB ABI KRV 24 = KRV 21 := rfl
  rw [e24] at hv
  change wordAccK 20520 15 (mask 15) (pidn 20520 15) AB ABI kWordsAB[0]! = K0
  rw [ew, hv.2 _ (PermJ3_of_canon cnPid), pcomp_pidnJ (by norm_num) (by norm_num) hv.1.1]
  exact Nat.eq_of_beq_eq_true rv21

theorem k1_wordJ : wordK 20520 15 (mask 15) (pidn 20520 15) AB ABI kWordsAB[1]! = K1 := by
  have ew : kWordsAB[1]! = exG rlJ 29 31 := by decide +kernel
  have hv := slp_val 29 31 (by decide +kernel)
  have e31 : symVG AB ABI KRV 31 = KRV 28 := rfl
  rw [e31] at hv
  change wordAccK 20520 15 (mask 15) (pidn 20520 15) AB ABI kWordsAB[1]! = K1
  rw [ew, hv.2 _ (PermJ3_of_canon cnPid), pcomp_pidnJ (by norm_num) (by norm_num) hv.1.1]
  exact Nat.eq_of_beq_eq_true rv28

theorem cnK0 : CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) K0 = true := by
  rw [← canonKB_eq]
  quickRfl

theorem cnKI0 : CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) KI0 = true := by
  rw [← canonKB_eq]
  quickRfl

theorem cnK1 : CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) K1 = true := by
  rw [← canonKB_eq]
  quickRfl

theorem cnKI1 : CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) KI1 = true := by
  rw [← canonKB_eq]
  quickRfl

theorem pcK0 : pcomp 20520 15 (mask 15) K0 KI0 = pidn 20520 15 := by
  rw [← pcompB_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pcK1 : pcomp 20520 15 (mask 15) K1 KI1 = pidn 20520 15 := by
  rw [← pcompB_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem ki0_eq : Nat.beq KI0 (pinvS 20520 15 (mask 15) K0) = true := by
  rw [CFSG.KS.PinvS.pinvS_of_pcomp cnK0 cnKI0 pcK0]
  exact Nat.beq_refl KI0

theorem ki1_eq : Nat.beq KI1 (pinvS 20520 15 (mask 15) K1) = true := by
  rw [CFSG.KS.PinvS.pinvS_of_pcomp cnK1 cnKI1 pcK1]
  exact Nat.beq_refl KI1

@[expose] def rlSJ : List (Int × Int) :=
  [(-2, 1), (3, 1), (2, -1), (2, 1), (4, 3), (7, 4), (8, 1), (2, 5), (10, 6), (1, -2), (12, -2),
    (13, -1), (6, 1), (15, 5), (16, 3), (17, 2)]

@[expose] noncomputable def sRuleJ (k : Nat) : Bool := ruleG 20520 15 KK KKI SRV rlSJ k

end CertificateChecks.KernelSchreierFam.J3Cq

#kon_slices CertificateChecks.KernelSchreierFam.J3Cq.sRuleJ 0 16
#kon_join CertificateChecks.KernelSchreierFam.J3Cq.sRuleJAll
  CertificateChecks.KernelSchreierFam.J3Cq.sRuleJ 16

namespace CertificateChecks.KernelSchreierFam.J3Cq

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SchreierFam CFSG.KS.SporSch
  CFSG.ClassicalInvolution.J3Data

theorem rlSJ_ord : ∀ k < rlSJ.length,
    ((rlSJ.getD k (0, 0)).1 < 3 ∨ ((rlSJ.getD k (0, 0)).1 - 3).toNat < k) ∧
    ((rlSJ.getD k (0, 0)).2 < 3 ∨ ((rlSJ.getD k (0, 0)).2 - 3).toNat < k) := by
  decide +kernel

theorem PermJ3_KK : ∀ h, PermJ3 20520 15 (KK h) := fun h => by
  unfold KK
  generalize Nat.beq h (nat_lit 0) = b
  cases b with
  | false => exact PermJ3_of_canon cnK1
  | true => exact PermJ3_of_canon cnK0

theorem PermJ3_KKI : ∀ h, PermJ3 20520 15 (KKI h) := fun h => by
  unfold KKI
  generalize Nat.beq h (nat_lit 0) = b
  cases b with
  | false => exact PermJ3_of_canon cnKI1
  | true => exact PermJ3_of_canon cnKI0

theorem slpS_val : ∀ (f : Nat) (z : Int),
    (z < 3 ∨ ((z - 3).toNat < f ∧ (z - 3).toNat < rlSJ.length)) →
    PermJ3 20520 15 (symVG KK KKI SRV z) ∧ ∀ T, PermJ3 20520 15 T →
      wordAccK 20520 15 (mask 15) T KK KKI (exG rlSJ f z) =
        pcomp 20520 15 (mask 15) (symVG KK KKI SRV z) T :=
  exG_val (by norm_num) (by norm_num) PermJ3_KK PermJ3_KKI rlSJ_ord fun k hk => sRuleJAll k hk

theorem srvS0 : Nat.beq (SY.S 0) (SRV 6) = true := by quickRfl

theorem srvS1 : Nat.beq (SY.S 1) (SRV 8) = true := by quickRfl

theorem srvS2 : Nat.beq (SY.S 2) (SRV 11) = true := by quickRfl

theorem srvS3 : Nat.beq (SY.S 3) (SRV 15) = true := by quickRfl

theorem sWordJ {wd : List Int} {z : Int} {k : Nat} (ew : wd = exG rlSJ 16 z)
    (hz : z < 3 ∨ ((z - 3).toNat < 16 ∧ (z - 3).toNat < rlSJ.length))
    (e : symVG KK KKI SRV z = SRV k) :
    wordK 20520 15 (mask 15) (pidn 20520 15) KK KKI wd = SRV k := by
  have hv := slpS_val 16 z hz
  rw [e] at hv
  change wordAccK 20520 15 (mask 15) (pidn 20520 15) KK KKI wd = SRV k
  rw [ew, hv.2 _ (PermJ3_of_canon cnPid), pcomp_pidnJ (by norm_num) (by norm_num) hv.1.1]

theorem s0_eq :
    Nat.beq (SY.S 0) (wordK 20520 15 (mask 15) (pidn 20520 15) KK KKI sWordsK[0]!) = true := by
  rw [sWordJ (wd := sWordsK[0]!) (z := 9) (k := 6) (by decide +kernel) (by decide +kernel) rfl]
  exact srvS0

theorem s1_eq :
    Nat.beq (SY.S 1) (wordK 20520 15 (mask 15) (pidn 20520 15) KK KKI sWordsK[1]!) = true := by
  rw [sWordJ (wd := sWordsK[1]!) (z := 11) (k := 8) (by decide +kernel) (by decide +kernel) rfl]
  exact srvS1

theorem s2_eq :
    Nat.beq (SY.S 2) (wordK 20520 15 (mask 15) (pidn 20520 15) KK KKI sWordsK[2]!) = true := by
  rw [sWordJ (wd := sWordsK[2]!) (z := 14) (k := 11) (by decide +kernel) (by decide +kernel) rfl]
  exact srvS2

theorem s3_eq :
    Nat.beq (SY.S 3) (wordK 20520 15 (mask 15) (pidn 20520 15) KK KKI sWordsK[3]!) = true := by
  rw [sWordJ (wd := sWordsK[3]!) (z := 18) (k := 15) (by decide +kernel) (by decide +kernel) rfl]
  exact srvS3

theorem rc0 : Nat.beq (rcnt (SY.LR 0)) 128 = true := by quickRfl

theorem cqNeg0 : cqSl [] 3 = false := by
  unfold cqSl cqK
  rw [← pcompB_eq]
  decide +kernel

theorem cqW0_eq : Nat.beq K0 (wordK 20520 15 KK [0]) = true := by
  unfold CFSG.KS.SchreierFam.wordK
  rw [← pcompB_eq]
  quickRfl

theorem cqW1_eq : Nat.beq W1 (wordK 20520 15 KK [0, 0]) = true := by
  unfold CFSG.KS.SchreierFam.wordK
  rw [← pcompB_eq]
  quickRfl

theorem cnW1 : CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) W1 = true := by
  rw [← canonKB_eq]
  quickRfl

theorem cnW1I : CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) W1I = true := by
  rw [← canonKB_eq]
  quickRfl

theorem pcW1 : pcomp 20520 15 (mask 15) W1 W1I = pidn 20520 15 := by
  rw [← pcompB_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem cqW1I_eq : Nat.beq W1I (pinvS 20520 15 (mask 15) W1) = true := by
  rw [CFSG.KS.PinvS.pinvS_of_pcomp cnW1 cnW1I pcW1]
  exact Nat.beq_refl W1I

theorem cqWS_ok : ∀ p ∈ cqWS, ∃ l ∈ cqWords,
    wordK 20520 15 KK l = p.1 ∧ pinvS 20520 15 (mask 15) p.1 = p.2 := by
  intro p hp
  simp only [cqWS, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨[0], by decide, (Nat.eq_of_beq_eq_true cqW0_eq).symm, (Nat.eq_of_beq_eq_true ki0_eq).symm⟩
  · exact ⟨[0, 0], by decide, (Nat.eq_of_beq_eq_true cqW1_eq).symm,
      (Nat.eq_of_beq_eq_true cqW1I_eq).symm⟩

theorem rcJ1 : Nat.beq (rcnt (SY.LR 1)) 1 = true := by quickRfl

theorem rcJ2 : Nat.beq (rcnt (SY.LR 2)) 1 = true := by quickRfl

theorem tr1_id :
    Nat.beq (trAt 20520 (20520 * 15) SY.LR SY.TR 1 0) (pidn 20520 15) = true := by quickRfl

theorem tr2_id :
    Nat.beq (trAt 20520 (20520 * 15) SY.LR SY.TR 2 0) (pidn 20520 15) = true := by quickRfl

theorem cqK_of_cqKQ {n w R a c1 c2 : Nat} {G : Nat → Nat} {L : List (List Nat)}
    {WS : List (Nat × Nat)} {T : Nat → Nat → Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hWS : ∀ p ∈ WS, ∃ l ∈ L, wordK n w G l = p.1 ∧ pinvS n w (mask w) p.1 = p.2)
    (r1 : Nat.beq c1 1 = true) (r2 : Nat.beq c2 1 = true)
    (h1 : Nat.beq (T 1 0) (pidn n w) = true) (h2 : Nat.beq (T 2 0) (pidn n w) = true)
    (h : cqTG n w R WS T a = true) :
    allN c1 (fun b => allN c2 fun c =>
      cqK n w R G L (pcomp n w (mask w) (pcomp n w (mask w) (T 0 a) (T 1 b)) (T 2 c))) = true := by
  unfold cqTG at h
  obtain ⟨h0, h⟩ := bAnd_tJ h
  open CFSG.KS.Raw.Orb in
  refine allN_iff.2 fun b hb => allN_iff.2 fun c hc => ?_
  obtain rfl : b = 0 := Nat.lt_one_iff.1 (lt_of_lt_of_eq hb (Nat.eq_of_beq_eq_true r1))
  obtain rfl : c = 0 := Nat.lt_one_iff.1 (lt_of_lt_of_eq hc (Nat.eq_of_beq_eq_true r2))
  exact cqK_of_cqKP (lt_trans hn (by norm_num)) hWS
    ((cqKQ_eq hn hw (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)
      (Nat.eq_of_beq_eq_true h0)).symm.trans h)

theorem cqS_of_cqT {a : Nat} (h : cqT a = true) : cqS a = true :=
  cqK_of_cqKQ (n := 20520) (w := 15) (R := A) (a := a) (c1 := rcnt (SY.LR 1))
    (c2 := rcnt (SY.LR 2)) (G := KK) (L := cqWords) (WS := cqWSel a)
    (T := trAt 20520 (20520 * 15) SY.LR SY.TR) (by norm_num) (by norm_num)
    (fun p hp => cqWS_ok p (cqWSel_sub a p hp)) rcJ1 rcJ2 tr1_id tr2_id h

@[expose] def cqSec : Nat := 217993715827280768277315887198258594848

@[expose] def cqPar : Nat :=
  520071165998607231345088597417454245856562518292848327866358636963471318608187982294729324458067131491862348538301167914570044025805342719228384239006657111217443198936420461436839271029765072089165622878701223924514987653093795588514426613816528636465599426531078176768

@[expose] noncomputable def cqParJ (a : Nat) : Nat := fld(cqPar, Nat.mul (nat_lit 7) a, mask (nat_lit 7))

@[expose] noncomputable def cqSecJ (a : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight cqSec a) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def cqX4 (w C W WI x : Nat) : Nat :=
  pg w (mask w) C (pg w (mask w) W (pg w (mask w) C (pg w (mask w) WI x)))

@[expose] noncomputable def cqV (a b : Nat) : Bool :=
  bAnd(Nat.blt b (nat_lit 128), bAnd(bIf(cqSecJ b, false, true),
    bAnd(Nat.beq (trAt 20520 (20520 * 15) SY.LR SY.TR 0 a)
      (SY.TRI (Nat.add (roff 20520 (20520 * 15) (SY.LR 0)) b)),
    bAnd(bIf(sqNe 20520 15 A (trAt 20520 (20520 * 15) SY.LR SY.TR 0 b)
      (trAt 20520 (20520 * 15) SY.LR SY.TR 1 0) (trAt 20520 (20520 * 15) SY.LR SY.TR 2 0)
      0, false, true),
    strictB (cqX4 15 (trAt 20520 (20520 * 15) SY.LR SY.TR 0 a) ((cqWSel b).headD (0, 0)).1
      ((cqWSel b).headD (0, 0)).2 (nat_lit 0)) fun x =>
      bIf(Nat.beq x (nat_lit 0), false, bIf(Nat.beq x (pg 15 (mask 15) A (nat_lit 0)), false,
        true))))))

@[expose] noncomputable def cqU (a : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (cqT a) (cqV a (cqParJ a)) (cqSecJ a)

theorem invo_conjJ {n : Nat} {c c' w wi : Nat → Nat} (hc : ∀ i < n, c i < n)
    (hw : ∀ i < n, w i < n) (hwi : ∀ i < n, wi i < n) (h1 : ∀ i < n, c' (c i) = i)
    (h3 : ∀ i < n, wi (w i) = i) (h4 : ∀ i < n, w (wi i) = i)
    (hX : ∀ i < n, c (w (c (wi (c (w (c (wi i))))))) = i) :
    ∀ i < n, c' (w (c' (wi (c' (w (c' (wi i))))))) = i := by
  have hY : ∀ j < n, w (c (wi (c j))) < n := fun j hj => hw _ (hc _ (hwi _ (hc j hj)))
  have key : ∀ j < n, c' (w (c' (wi (w (c (wi (c j))))))) = j := fun j hj => by
    rw [h3 _ (hc _ (hwi _ (hc j hj))), h1 _ (hwi _ (hc j hj)), h4 _ (hc j hj), h1 j hj]
  have hYY : ∀ j < n, w (c (wi (c (w (c (wi (c j))))))) = j := fun j hj => by
    have e := congrArg c' (hX (c j) (hc j hj))
    rwa [h1 _ (hY _ (hY j hj)), h1 j hj] at e
  intro i hi
  have e1 := key _ (hY i hi)
  rw [hYY i hi] at e1
  rw [e1]
  exact key i hi

theorem pg4J {C W WI i : Nat} (hi : i < 20520) :
    pg 15 (mask 15) (pcomp 20520 15 (mask 15) C (pcomp 20520 15 (mask 15) W
      (pcomp 20520 15 (mask 15) C WI))) i = cqX4 15 C W WI i := by
  have hn : (20520 : Nat) < 2 ^ 32 := by norm_num
  rw [CFSG.KS.PF.pg_pcomp hn hi, CFSG.KS.PF.pg_pcomp hn hi, CFSG.KS.PF.pg_pcomp hn hi]
  rfl

theorem cqWS_inv : ∀ p ∈ cqWS, CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) p.1 = true ∧
    CFSG.KS.Prim.canonK 20520 15 (mask 15) (20520 * 15) p.2 = true ∧
    pcomp 20520 15 (mask 15) p.1 p.2 = pidn 20520 15 := by
  intro p hp
  simp only [cqWS, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨cnK0, cnKI0, pcK0⟩
  · exact ⟨cnW1, cnW1I, pcW1⟩

theorem cqWSel_hd (b : Nat) : ∀ p ∈ cqWSel b, p = (cqWSel b).headD (0, 0) := by
  intro p
  unfold cqWSel
  cases Nat.beq (Nat.land (Nat.shiftRight cqSel b) (nat_lit 1)) (nat_lit 1) with
  | false => exact fun hp => List.mem_singleton.1 hp
  | true => exact fun hp => List.mem_singleton.1 hp

theorem cqTG_wit {n w R a : Nat} {WS : List (Nat × Nat)} {T : Nat → Nat → Nat}
    (h : cqTG n w R WS T a = true) (hs : sqNe n w R (T 0 a) (T 1 0) (T 2 0) 0 = false) :
    WS.any (fun p => invoNeI n w R (T 1 0)
      (pcompB n w (T 0 a) (pcompB n w p.1 (pcompB n w (T 0 a) p.2)))) = true := by
  unfold cqTG at h
  obtain ⟨-, h⟩ := bAnd_tJ h
  unfold cqKQ at h
  rw [hs] at h
  exact h

theorem bIf2_fJ {c d : Bool} (h : bIf(c, false, bIf(d, false, true)) = true) :
    c = false ∧ d = false := by
  cases c <;> cases d <;> simp_all

theorem cqS_sec {a b : Nat}
    (hpa : permOK 20520 15 (mask 15) (20520 * 15) (trAt 20520 (20520 * 15) SY.LR SY.TR 0 a)
      (SY.TRI (Nat.add (roff 20520 (20520 * 15) (SY.LR 0)) a)) = true)
    (hpb : permOK 20520 15 (mask 15) (20520 * 15) (trAt 20520 (20520 * 15) SY.LR SY.TR 0 b)
      (SY.TRI (Nat.add (roff 20520 (20520 * 15) (SY.LR 0)) b)) = true)
    (hb : cqT b = true) (h : cqV a b = true) : cqS a = true := by
  have hn : (20520 : Nat) < 2 ^ 32 := by norm_num
  have hn' : (20520 : Nat) < 16777216 := by norm_num
  have hw : (20520 : Nat) + 1 < 2 ^ 15 := by norm_num
  unfold cqV at h
  obtain ⟨-, h⟩ := bAnd_tJ h
  obtain ⟨-, h⟩ := bAnd_tJ h
  obtain ⟨heq, h⟩ := bAnd_tJ h
  obtain ⟨hsq, hpt⟩ := bAnd_tJ h
  rw [strictB_eqJ] at hpt
  obtain ⟨hp1, hp2⟩ := bIf2_fJ hpt
  obtain ⟨p, hp, hX⟩ := List.any_eq_true.1 (cqTG_wit (n := 20520) (w := 15) (R := A)
    (WS := cqWSel b) (T := trAt 20520 (20520 * 15) SY.LR SY.TR) hb (bIf_fJ hsq))
  rw [← cqWSel_hd b p hp] at hp1 hp2
  obtain ⟨cW, cWI, pW⟩ := cqWS_inv p (cqWSel_sub b p hp)
  obtain ⟨-, -, hinv⟩ := CFSG.KS.PinvS.inv_of_pcomp cW cWI pW
  have rW := (CFSG.KS.PF.canon_facts cW).2.2.2
  have rWI := (CFSG.KS.PF.canon_facts cWI).2.2.2
  unfold invoNeI at hX
  obtain ⟨hXX, -⟩ := bAnd_tJ hX
  rw [pcompB_eq, Nat.eq_of_beq_eq_true tr1_id] at hXX
  have hXX := Nat.eq_of_beq_eq_true hXX
  obtain ⟨shra, -, fa⟩ := CFSG.KS.Raw.Orb.permOK_facts hpa
  obtain ⟨-, -, fb⟩ := CFSG.KS.Raw.Orb.permOK_facts hpb
  have heq := Nat.eq_of_beq_eq_true heq
  unfold cqS cqSl
  open CFSG.KS.Raw.Orb in
  refine allN_iff.2 fun b' hb' => allN_iff.2 fun c hc => ?_
  obtain rfl : b' = 0 := Nat.lt_one_iff.1 (lt_of_lt_of_eq hb' (Nat.eq_of_beq_eq_true rcJ1))
  obtain rfl : c = 0 := Nat.lt_one_iff.1 (lt_of_lt_of_eq hc (Nat.eq_of_beq_eq_true rcJ2))
  rw [Nat.eq_of_beq_eq_true tr1_id, Nat.eq_of_beq_eq_true tr2_id, pcomp_pidnJ hn' hw shra,
    pcomp_pidnJ hn' hw shra]
  rw [heq] at fa hp1 hp2 ⊢
  generalize trAt 20520 (20520 * 15) SY.LR SY.TR 0 b = Cb at fb hXX
  generalize SY.TRI (Nat.add (roff 20520 (20520 * 15) (SY.LR 0)) b) = C at fa fb hp1 hp2 ⊢
  have hp1' : Nat.beq (cqX4 15 C p.1 p.2 0) 0 = false := hp1
  have hp2' : Nat.beq (cqX4 15 C p.1 p.2 0) (pg 15 (mask 15) A 0) = false := hp2
  have rb : ∀ i < 20520, pg 15 (mask 15) Cb i < 20520 := fun i hi => (fb i hi).1
  have ra : ∀ i < 20520, pg 15 (mask 15) C i < 20520 := fun i hi => (fa i hi).1
  have hXp : ∀ i < 20520, cqX4 15 Cb p.1 p.2 (cqX4 15 Cb p.1 p.2 i) = i := fun i hi => by
    have e := congrArg (fun q => pg 15 (mask 15) q i) hXX
    beta_reduce at e
    rw [CFSG.KS.PF.pg_pcomp hn hi, pg4J hi, pg4J (i := cqX4 15 Cb p.1 p.2 i) (rb _ (rW _ (rb _ (rWI i hi)))),
      CFSG.KS.PF.pg_pidn hn' hw hi] at e
    exact e
  have hX' := invo_conjJ rb rW rWI (fun i hi => (fb i hi).2) (fun i hi => (hinv i hi).2)
    (fun i hi => (hinv i hi).1) hXp
  unfold cqK
  cases hbq : Nat.beq (pcomp 20520 15 (mask 15) C C) A with
  | false => rfl
  | true =>
    obtain ⟨l, hl, hWl, hWIl⟩ := cqWS_ok p (cqWSel_sub b p hp)
    refine List.any_eq_true.2 ⟨l, hl, ?_⟩
    unfold cjK
    rw [hWl, hWIl]
    have hXX' : pcomp 20520 15 (mask 15)
        (pcomp 20520 15 (mask 15) C (pcomp 20520 15 (mask 15) p.1 (pcomp 20520 15 (mask 15) C p.2)))
        (pcomp 20520 15 (mask 15) C (pcomp 20520 15 (mask 15) p.1 (pcomp 20520 15 (mask 15) C p.2)))
        = pidn 20520 15 :=
      CFSG.KS.PF.eq_of_fields (by norm_num) (CFSG.KS.PF.pcomp_shr _ _ hn (by norm_num))
        (CFSG.KS.PF.canon_facts cnPid).2.2.1 fun i hi => by
          rw [CFSG.KS.PF.pg_pcomp hn hi, pg4J hi,
            pg4J (i := cqX4 15 C p.1 p.2 i) (ra _ (rW _ (ra _ (rWI i hi)))),
            CFSG.KS.PF.pg_pidn hn' hw hi]
          exact hX' i hi
    have hne1 : Nat.beq (pcomp 20520 15 (mask 15) C
        (pcomp 20520 15 (mask 15) p.1 (pcomp 20520 15 (mask 15) C p.2))) (pidn 20520 15) = false := by
      cases e : Nat.beq (pcomp 20520 15 (mask 15) C
          (pcomp 20520 15 (mask 15) p.1 (pcomp 20520 15 (mask 15) C p.2))) (pidn 20520 15) with
      | false => rfl
      | true =>
        have e2 := congrArg (fun q => pg 15 (mask 15) q 0) (Nat.eq_of_beq_eq_true e)
        beta_reduce at e2
        rw [pg4J (by norm_num), CFSG.KS.PF.pg_pidn hn' hw (by norm_num)] at e2
        rw [e2] at hp1'
        exact absurd hp1' (by decide)
    have hne2 : Nat.beq (pcomp 20520 15 (mask 15) C
        (pcomp 20520 15 (mask 15) p.1 (pcomp 20520 15 (mask 15) C p.2))) A = false := by
      cases e : Nat.beq (pcomp 20520 15 (mask 15) C
          (pcomp 20520 15 (mask 15) p.1 (pcomp 20520 15 (mask 15) C p.2))) A with
      | false => rfl
      | true =>
        have e2 := congrArg (fun q => pg 15 (mask 15) q 0) (Nat.eq_of_beq_eq_true e)
        beta_reduce at e2
        rw [pg4J (by norm_num)] at e2
        rw [e2, Nat.beq_refl] at hp2'
        exact absurd hp2' (by decide)
    unfold invoNe
    rw [hXX', Nat.beq_refl, hne1, hne2]

end CertificateChecks.KernelSchreierFam.J3Cq

#kon_slices CertificateChecks.KernelSchreierFam.J3Cq.cqU 0 128
#kon_join CertificateChecks.KernelSchreierFam.J3Cq.cqUAll
  CertificateChecks.KernelSchreierFam.J3Cq.cqU 128

namespace CertificateChecks.KernelSchreierFam.J3Cq

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SchreierFam CFSG.KS.SporSch

theorem cqSAll
    (hP : ∀ k < 128, permOK 20520 15 (mask 15) (20520 * 15) (trAt 20520 (20520 * 15) SY.LR SY.TR 0 k)
      (SY.TRI (Nat.add (roff 20520 (20520 * 15) (SY.LR 0)) k)) = true) :
    ∀ s, s < 128 → cqS s = true := fun s hs => by
  have hU := cqUAll s hs
  unfold cqU at hU
  cases e : cqSecJ s with
  | false =>
    rw [e] at hU
    exact cqS_of_cqT hU
  | true =>
    rw [e] at hU
    have hV : cqV s (cqParJ s) = true := hU
    have h' := hV
    unfold cqV at h'
    obtain ⟨hlt, h'⟩ := bAnd_tJ h'
    obtain ⟨hsb, -⟩ := bAnd_tJ h'
    have hb := Nat.blt_eq.mp hlt
    have hbU := cqUAll _ hb
    unfold cqU at hbU
    rw [bIf_fJ hsb] at hbU
    exact cqS_sec (hP s hs) (hP _ hb) hbU hV

end CertificateChecks.KernelSchreierFam.J3Cq
