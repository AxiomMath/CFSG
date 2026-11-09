module

public import Certificates.Kernel.TitsOver.Three.Enum
public import Certificates.Kernel.TitsOver.Three.Sides
public import Certificates.Kernel.TitsOver.Three.Data
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Kernel.Sporadic.Tits.Words2264
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.Kernel.TitsOver.Check
public import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import Certificates.Kernel.TitsOver.Three.DEq
public import Certificates.Kernel.TitsOver.Three.WordSuf
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.KS.TitsOver CertificateChecks.KernelSpor.Tits2264 CFSG.StandardType.TitsThree

theorem k_pg : allN 2 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    (pWords[j]!) (PE.G j), canonK 1755 11 (mask 11) (1755 * 11) (PE.G j))) = true := by
  rw [dk_eq, dik_eq]
  quickRfl
theorem k_ph : penumHdK (pidn 1755 11) PE.cnt 27 PE.T PE.PL = true := by quickRfl
theorem k_psl : penumSlK 1755 11 (mask 11) (1755 * 11) false PE.G PE.GI PE.k PE.cnt PE.T PE.PL
    PE.POS PE.SRT PE.SRI 0 27 = true := by quickRfl
theorem k_pgi : allN 2 (fun l => permOK 1755 11 (mask 11) (1755 * 11) (PE.G l) (PGI l)) = true := by
  quickRfl
theorem k_ng : allN 4 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    (nWords[j]!) (NE.G j), canonK 1755 11 (mask 11) (1755 * 11) (NE.G j))) = true := by
  rw [dk_eq, dik_eq]
  quickRfl
theorem k_nh : penumHdK (pidn 1755 11) NE.cnt 216 NE.T NE.PL = true := by quickRfl
theorem k_ngi : allN 4 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (NE.G j) (NGI j)) = true := by
  quickRfl
theorem k_norm : allN 4 (fun j => allN 2 (fun i =>
    bAnd(conjInK 1755 11 PE.cnt PE.T (NE.G j) (NGI j) (PE.G i)
      (r32 NH (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 1755 11 PE.cnt PE.T (NGI j) (NE.G j) (PE.G i)
      (r32 NH (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem k_sz : szOK 1755 11 = true := by quickRfl
theorem k_dc : bAnd(canonK 1755 11 (mask 11) (1755 * 11) (DKL 0),
    bAnd(canonK 1755 11 (mask 11) (1755 * 11) (DKL 1),
    bAnd(canonK 1755 11 (mask 11) (1755 * 11) (DIL 0),
      canonK 1755 11 (mask 11) (1755 * 11) (DIL 1)))) = true := by quickRfl
theorem k_dS (k : Nat) :
    canonK 1755 11 (mask 11) (1755 * 11) (nIf(Nat.beq k 0, DKL 0, DKL 1)) = true := by
  have hd := k_dc
  simp only [PK.bAnd_eq, Bool.and_eq_true] at hd
  exact canonK_letter (S := fun _ => DKL 0) (SI := fun _ => DKL 1) (fun _ => hd.1)
    (fun _ => hd.2.1) _ 0 0
theorem k_dSI (k : Nat) :
    canonK 1755 11 (mask 11) (1755 * 11) (nIf(Nat.beq k 0, DIL 0, DIL 1)) = true := by
  have hd := k_dc
  simp only [PK.bAnd_eq, Bool.and_eq_true] at hd
  exact canonK_letter (S := fun _ => DIL 0) (SI := fun _ => DIL 1) (fun _ => hd.2.2.1)
    (fun _ => hd.2.2.2) _ 0 0
@[expose] noncomputable def wDK (u : List Int) : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) (fun k => nIf(Nat.beq k 0, DKL 0, DKL 1))
    (fun k => nIf(Nat.beq k 0, DIL 0, DIL 1)) u
@[expose] def sgW (s j : Nat) : List Int := (rGenWords.getD s []).getD j []
@[expose] def cgW (s j : Nat) : List Int := (conjugatorWords.getD s []).getD j []
@[expose] noncomputable def kcjF (s : Nat) (G : Nat → Nat) : Bool :=
  strictB (wDK (sgW s 0)) fun A => strictB (wDK (sgW s 1)) fun B =>
  strictB (wDK (cgW s 0)) fun C =>
  strictB (wDK (CFSG.StandardType.TitsOvergroup.invWord (cgW s 0))) fun I =>
  strictB (wDK (cgW s 1)) fun D =>
  strictB (wDK (CFSG.StandardType.TitsOvergroup.invWord (cgW s 1))) fun J =>
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) I, bAnd(canonK 1755 11 (mask 11) (1755 * 11) J,
  bAnd(Nat.beq (G 0) A, bAnd(Nat.beq (G 1) B,
  bAnd(Nat.beq (G 2) (pcomp 1755 11 (mask 11) C (pcomp 1755 11 (mask 11) A I)),
  bAnd(Nat.beq (G 3) (pcomp 1755 11 (mask 11) C (pcomp 1755 11 (mask 11) B I)),
  bAnd(Nat.beq (G 4) (pcomp 1755 11 (mask 11) D (pcomp 1755 11 (mask 11) A J)),
    Nat.beq (G 5) (pcomp 1755 11 (mask 11) D (pcomp 1755 11 (mask 11) B J)))))))))

theorem sg_of_kcj {s : Nat} {G : Nat → Nat} (hc : kcjF s G = true)
    (hl : allN 6 (fun j => bAnd(lettersK 2 ((lWords s)[j]!),
      canonK 1755 11 (mask 11) (1755 * 11) (G j))) = true) :
    allN 6 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11)
      (fun k => nIf(Nat.beq k 0, DKL 0, DKL 1)) (fun k => nIf(Nat.beq k 0, DIL 0, DIL 1)) 2
      ((lWords s)[j]!) (G j), canonK 1755 11 (mask 11) (1755 * 11) (G j))) = true := by
  have hS := k_dS
  have hSI := k_dSI
  unfold kcjF at hc
  simp only [CFSG.KS.PF.strictB_eqP, PK.bAnd_eq, Bool.and_eq_true] at hc
  obtain ⟨hI, hJ, h0, h1, h2, h3, h4, h5⟩ := hc
  have hw : ∀ j < 6, Nat.beq (wDK ((lWords s)[j]!)) (G j) = true := by
    intro j hj
    match j, hj with
    | 0, _ =>
      rw [Nat.eq_of_beq_eq_true h0]
      exact Nat.beq_refl _
    | 1, _ =>
      rw [Nat.eq_of_beq_eq_true h1]
      exact Nat.beq_refl _
    | 2, _ =>
      have e : (lWords s)[2]! = cgW s 0 ++ sgW s 0 ++
        CFSG.StandardType.TitsOvergroup.invWord (cgW s 0) := rfl
      rw [Nat.eq_of_beq_eq_true h2, e]
      unfold wDK
      rw [wordK_conj hS hSI _ _ _ hI]
      exact Nat.beq_refl _
    | 3, _ =>
      have e : (lWords s)[3]! = cgW s 0 ++ sgW s 1 ++
        CFSG.StandardType.TitsOvergroup.invWord (cgW s 0) := rfl
      rw [Nat.eq_of_beq_eq_true h3, e]
      unfold wDK
      rw [wordK_conj hS hSI _ _ _ hI]
      exact Nat.beq_refl _
    | 4, _ =>
      have e : (lWords s)[4]! = cgW s 1 ++ sgW s 0 ++
        CFSG.StandardType.TitsOvergroup.invWord (cgW s 1) := rfl
      rw [Nat.eq_of_beq_eq_true h4, e]
      unfold wDK
      rw [wordK_conj hS hSI _ _ _ hJ]
      exact Nat.beq_refl _
    | 5, _ =>
      have e : (lWords s)[5]! = cgW s 1 ++ sgW s 1 ++
        CFSG.StandardType.TitsOvergroup.invWord (cgW s 1) := rfl
      rw [Nat.eq_of_beq_eq_true h5, e]
      unfold wDK
      rw [wordK_conj hS hSI _ _ _ hJ]
      exact Nat.beq_refl _
  refine PK.allN_iff.2 fun j hj => ?_
  have l := PK.allN_iff.1 hl j hj
  simp only [PK.bAnd_eq, Bool.and_eq_true] at l ⊢
  refine ⟨?_, l.2⟩
  unfold wordEqK
  simp only [PK.bAnd_eq, Bool.and_eq_true]
  exact ⟨k_sz, l.1, hw j hj⟩

theorem k_cj0 : kcjF 0 S0E.G = true := by quickRfl
theorem k_cj1 : kcjF 1 S1E.G = true := by quickRfl
theorem k_sl0 : allN 6 (fun j => bAnd(lettersK 2 ((lWords 0)[j]!),
    canonK 1755 11 (mask 11) (1755 * 11) (S0E.G j))) = true := by quickRfl
theorem k_sl1 : allN 6 (fun j => bAnd(lettersK 2 ((lWords 1)[j]!),
    canonK 1755 11 (mask 11) (1755 * 11) (S1E.G j))) = true := by quickRfl
theorem k_sg0 : allN 6 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    ((lWords 0)[j]!) (S0E.G j), canonK 1755 11 (mask 11) (1755 * 11) (S0E.G j))) = true := by
  rw [dk_eq, dik_eq]
  exact sg_of_kcj k_cj0 k_sl0
theorem k_sg1 : allN 6 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    ((lWords 1)[j]!) (S1E.G j), canonK 1755 11 (mask 11) (1755 * 11) (S1E.G j))) = true := by
  rw [dk_eq, dik_eq]
  exact sg_of_kcj k_cj1 k_sl1
@[expose] noncomputable def sgF (A : List (List Int)) (G : Nat → Nat) (j : Nat) : Bool :=
  bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2 (A[j]!) (G j),
    canonK 1755 11 (mask 11) (1755 * 11) (G j))

theorem sgF_append {A B : List (List Int)} {G G₁ G₂ : Nat → Nat} {a b : Nat} (hA : A.length = a)
    (h₁ : allN a (sgF A G₁) = true) (h₂ : allN b (sgF B G₂) = true)
    (e₁ : allN a (fun j => Nat.beq (G j) (G₁ j)) = true)
    (e₂ : allN b (fun j => Nat.beq (G (a + j)) (G₂ j)) = true) :
    allN (a + b) (sgF (A ++ B) G) = true := by
  refine PK.allN_iff.2 fun j hj => ?_
  by_cases hja : j < a
  · have hl : (A ++ B)[j]! = A[j]! := by
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by omega : j < A.length)]
    have g := Nat.eq_of_beq_eq_true (PK.allN_iff.1 e₁ j hja)
    have h := PK.allN_iff.1 h₁ j hja
    unfold sgF at h ⊢
    rw [hl, g]
    exact h
  · have hjb : j - a < b := by omega
    have hl : (A ++ B)[j]! = B[j - a]! := by
      simp only [List.getElem!_eq_getElem?_getD,
        List.getElem?_append_right (by omega : A.length ≤ j), hA]
    have g := Nat.eq_of_beq_eq_true (PK.allN_iff.1 e₂ (j - a) hjb)
    have hj' : a + (j - a) = j := by omega
    rw [hj'] at g
    have h := PK.allN_iff.1 h₂ (j - a) hjb
    unfold sgF at h ⊢
    rw [hl, g]
    exact h

theorem k_sg2e0 : allN 6 (fun j => Nat.beq (S2E.G j) (S0E.G j)) = true := by quickRfl
theorem k_sg2e1 : allN 4 (fun j => Nat.beq (S2E.G (6 + j)) (NE.G j)) = true := by quickRfl
theorem k_sg3e0 : allN 6 (fun j => Nat.beq (S3E.G j) (S1E.G j)) = true := by quickRfl
theorem k_sg3e1 : allN 4 (fun j => Nat.beq (S3E.G (6 + j)) (NE.G j)) = true := by quickRfl
theorem k_sg2 : allN 10 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    ((mWords 0)[j]!) (S2E.G j), canonK 1755 11 (mask 11) (1755 * 11) (S2E.G j))) = true :=
  sgF_append (A := lWords 0) (B := nWords) (G := S2E.G) (a := 6) (b := 4) rfl k_sg0 k_ng
    k_sg2e0 k_sg2e1
theorem k_sg3 : allN 10 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    ((mWords 1)[j]!) (S3E.G j), canonK 1755 11 (mask 11) (1755 * 11) (S3E.G j))) = true :=
  sgF_append (A := lWords 1) (B := nWords) (G := S3E.G) (a := 6) (b := 4) rfl k_sg1 k_ng
    k_sg3e0 k_sg3e1
theorem k_sh0 : penumHdK (pidn 1755 11) S0E.cnt 5616 S0E.T S0E.PL = true := by quickRfl
theorem k_sh1 : penumHdK (pidn 1755 11) S1E.cnt 5616 S1E.T S1E.PL = true := by quickRfl
theorem k_sh2 : penumHdK (pidn 1755 11) S2E.cnt 11232 S2E.T S2E.PL = true := by quickRfl
theorem k_sh3 : penumHdK (pidn 1755 11) S3E.cnt 11232 S3E.T S3E.PL = true := by quickRfl
theorem k_sgi0 : allN 6 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (S0E.G j) (SGI0 j)) = true := by
  quickRfl
theorem k_sgi1 : allN 6 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (S1E.G j) (SGI1 j)) = true := by
  quickRfl

theorem k_r0 : Nat.beq (REP 0) (pidn 1755 11) = true := by quickRfl
@[expose] def rwSuf : List Nat :=
  [1, 1, 1, 1, 17, 17, 33, 33, 49, 65, 17, 49, 65, 33, 49, 81, 81, 97, 97, 113, 113, 129, 129, 161,
   177, 145, 161, 177, 225, 113, 193, 209, 209, 225, 129, 73792, 145, 241, 193, 98368, 177, 225,
   209, 241, 122944, 257, 257, 273, 273, 289, 305, 321, 337, 337, 353, 369, 385, 73808, 401, 465,
   481, 417, 417, 433, 433, 257, 98384, 82016, 289, 449, 449, 465, 321, 481, 561, 353, 497, 497,
   57536, 65728, 513, 513, 529, 529, 73888, 273, 106592, 305, 545, 545, 337, 561, 593, 417, 625,
   481, 401, 577, 98464, 657, 673, 465, 593, 609, 497, 689, 641, 122960, 344080, 673, 705, 561, 641,
   65776, 529, 721, 625, 689, 689, 657, 593, 123040, 721, 114928, 753, 753, 769, 769, 785, 785, 801,
   801, 57632, 41264, 49456, 41280, 833, 849, 849, 865, 865, 881, 65888, 897, 897, 913, 929, 1105,
   961, 993, 1009, 1009, 1025, 1041, 737, 1057, 1377, 801, 1409, 1137, 1153, 90432, 1169, 849, 1185,
   1185, 82288, 897, 1489, 1505, 1249, 1265, 1281, 1553, 1313, 1329, 1345, 1633, 1377, 785, 1393,
   1409, 1553, 945, 74176, 1441, 1441, 961, 1457, 1473, 1473, 1361, 115040, 1105, 1489, 1521, 1537,
   1553, 1697, 1569, 1585, 1585, 913, 1729, 1073, 1745, 107072, 1825, 977, 1665, 1665, 1681, 237760,
   1841, 1953, 1537, 1857, 1873, 123488, 1297, 1713, 1713, 106928, 1713, 1569, 164080, 1729, 1745,
   82624, 1633, 1793, 82464, 344224, 66192, 1761, 1153, 1505, 1521, 99008, 360672, 1793, 82592,
   344192, 1809, 172272, 1249, 1281, 90736, 344256, 123584, 246000, 1889, 1809, 1953, 1697, 1873,
   1729, 107040, 360688, 1649, 66272, 2033, 2033, 2065, 2097, 2097, 2113, 2129, 180512, 188704,
   2145, 147776, 2193, 2241, 50032, 2273, 172384, 2289, 2305, 2337, 99360, 2513, 2545, 2593, 50128,
   107696, 2433, 2433, 99328, 66560, 2881, 75216, 58432, 50256, 2545, 90928, 2945, 2577, 2177,
   90944, 2641, 2657, 58544, 42176, 2673, 50384, 2737, 66800, 2769, 2769, 99296, 66832, 74752,
   352449, 2865, 82848, 287008, 2913, 123904, 107312, 2929, 99936, 3009, 2225, 107360, 83536,
   279168, 3121, 82928, 74960, 3441, 124560, 352624, 3489, 115776, 3505, 221616, 3585, 116528,
   107936, 3265, 3313, 3729, 67136, 254400, 287360, 3649, 835696, 3569, 108112, 3249, 3873, 3937,
   3393, 3393, 2769, 156272, 123968, 107632, 3969, 106945, 3345, 2913, 3681, 116560, 124864, 3905,
   303488, 124144, 3121, 4001, 3985, 42864, 4081, 4097, 3633, 2529, 107808, 107712, 3713, 2977,
   2961, 91872, 124480, 2865, 3857, 246400, 91616, 3921, 42784, 115920, 115968, 4161, 59328, 108480,
   107888, 4129, 4145, 59216, 262816, 116672, 108432, 3585, 164576, 51200, 59392, 51264, 148272,
   4433, 51440, 59664, 67856, 860640, 197472, 255168, 92128, 83968, 92224, 173152, 860880, 165104,
   44096, 181536, 68368, 60816, 68608, 77344, 2056432, 4945, 206160, 4545, 345392, 223072, 92800,
   5873, 108449, 5217, 6353, 1008192, 101696, 370560, 44576, 295952, 118000, 746064, 247648, 174192,
   157888, 86672, 239712, 1933952, 582736, 223840, 485152, 550160, 49797]

@[expose] def rwN : Nat := rwSuf.foldr (fun c acc => Nat.add c (Nat.shiftLeft acc 24)) 0
@[expose] def rwC (i : Nat) : Nat := Nat.land (Nat.shiftRight rwN (Nat.mul 24 i)) 16777215
@[expose] def rwA (i : Nat) : Nat := Nat.shiftRight (rwC i) 13
@[expose] def rwS (i : Nat) : Nat := Nat.land (Nat.shiftRight (rwC i) 4) 511
@[expose] def rwK (i : Nat) : Nat := Nat.land (rwC i) 15
@[expose] def rwW (s : Nat) : List Int := if s = 0 then [] else repWords[s - 1]!

@[expose] def rwP (i : Nat) : Nat := if rwA i = 0 then 0 else (repWords[rwA i - 1]!).length
@[expose] def rwLs (i : Nat) : List Int := ((repWords[i]!).drop (rwP i)).take (rwK i)
@[expose] noncomputable def krwF (i : Nat) : Bool :=
  bAnd(Nat.blt (rwA i) (Nat.succ i),
    bAnd(Nat.blt (rwS i) (Nat.succ i),
    bAnd(decide ((repWords[i]!).take (rwP i) = rwW (rwA i)),
    bAnd(decide (((repWords[i]!).drop (rwP i)).drop (rwK i) = rwW (rwS i)),
      Nat.beq (if rwA i = 0 then wordKP 1755 11 (mask 11) (REP (rwS i))
          (fun k => nIf(Nat.beq k 0, DKL 0, DKL 1)) (fun k => nIf(Nat.beq k 0, DIL 0, DIL 1))
          (rwLs i)
        else pcomp 1755 11 (mask 11) (REP (rwA i)) (wordKP 1755 11 (mask 11) (REP (rwS i))
          (fun k => nIf(Nat.beq k 0, DKL 0, DKL 1)) (fun k => nIf(Nat.beq k 0, DIL 0, DIL 1))
          (rwLs i)))
        (REP (Nat.succ i))))))
@[expose] noncomputable def krwG (i : Nat) (u : List Int) : Bool :=
  bAnd(Nat.blt (rwA i) (Nat.succ i),
    bAnd(Nat.blt (rwS i) (Nat.succ i),
    bAnd(decide (u.take (rwP i) = rwW (rwA i)),
    bAnd(decide ((u.drop (rwP i)).drop (rwK i) = rwW (rwS i)),
      Nat.beq (if rwA i = 0 then wordKP 1755 11 (mask 11) (REP (rwS i))
          (fun k => nIf(Nat.beq k 0, DKL 0, DKL 1)) (fun k => nIf(Nat.beq k 0, DIL 0, DIL 1))
          ((u.drop (rwP i)).take (rwK i))
        else pcomp 1755 11 (mask 11) (REP (rwA i)) (wordKP 1755 11 (mask 11) (REP (rwS i))
          (fun k => nIf(Nat.beq k 0, DKL 0, DKL 1)) (fun k => nIf(Nat.beq k 0, DIL 0, DIL 1))
          ((u.drop (rwP i)).take (rwK i))))
        (REP (Nat.succ i))))))
@[expose] noncomputable def krwC (c : Nat) : Bool :=
  ((repWords.zipIdx.drop (32 * c)).take 32).all (fun p => krwG p.2 p.1)
#kc_each krwC 0 15
#kc_forall_chunks krw_all (fun c => krwC c = true) 15 CertificateChecks.KernelTitsOver.Three.krwC 1
@[expose] noncomputable def kriF (i : Nat) : Bool :=
  permOK 1755 11 (mask 11) (1755 * 11) (REP i) (REPI i)
@[expose] noncomputable def kriC (c : Nat) : Bool :=
  allN 32 (fun t => bIf(Nat.blt (Nat.add (Nat.mul c 32) t) 457, kriF (Nat.add (Nat.mul c 32) t),
    true))
#kc_each kriC 0 15
#kc_forall_chunks kri_all (fun c => kriC c = true) 15 CertificateChecks.KernelTitsOver.Three.kriC 1
theorem k_ri : allN 457 (fun i => permOK 1755 11 (mask 11) (1755 * 11) (REP i) (REPI i)) = true :=
  allN_of_guarded (f := kriF) (by decide) (by decide) kri_all
theorem k_rlet : repWords.all (lettersK 2) = true := by quickRfl
theorem k_rw : allN 456 (fun i => wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    (repWords[i]!) (REP (Nat.succ i))) = true := by
  rw [dk_eq, dik_eq]
  have hc : allN 456 krwF = true :=
    allN_of_zipIdx_chunks (l := repWords) (f := krwG) (n := 456) (w := 32) (m := 15) (by decide)
      (by decide) (by decide) krw_all
  have hv := wordK_of_split (n := 1755) (w := 11) (N := 456)
    (S := fun k => nIf(Nat.beq k 0, DKL 0, DKL 1)) (SI := fun k => nIf(Nat.beq k 0, DIL 0, DIL 1))
    (R := REP) (a := rwA) (s := rwS) (K := rwK) (W := fun i => repWords[i]!) k_dS k_dSI
    (fun i hi => canonK_of_permOK k_sz (PK.allN_iff.1 k_ri i hi)) (Nat.eq_of_beq_eq_true k_r0)
    (fun i hi => by
      have h := PK.allN_iff.1 hc i hi
      unfold krwF at h
      simp only [PK.bAnd_eq, Bool.and_eq_true] at h
      exact ⟨Nat.blt_eq.mp h.1, Nat.blt_eq.mp h.2.1, of_decide_eq_true h.2.2.1,
        of_decide_eq_true h.2.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2.2⟩)
  have hl : allN 456 (fun i => lettersK 2 (repWords[i]!)) = true :=
    allN_of_all (by decide) k_rlet
  refine PK.allN_iff.2 fun i hi => ?_
  have hw := hv i hi
  unfold wordEqK
  rw [hw, k_sz, PK.allN_iff.1 hl i hi]
  exact Nat.beq_refl _
theorem k_pts : allN 2 (fun t => bAnd(Nat.beq (pairData.fpPts[t]!) (r32 PT t),
    Nat.blt (r32 PT t) 1755)) = true := by quickRfl
theorem k_srt : allN NE.cnt (sortK 11 2 22 NE.cnt (r32 PT) NE.T FS KS) = true := by quickRfl
theorem k_cnt : allN 456 (fun i => Nat.beq (posCnt NE.cnt H (Nat.succ i)) (r32 CN (Nat.succ i))) =
    true := by quickRfl
theorem k_sum : Nat.beq ((List.range 457).foldl (fun s i => s + 216 * 216 /
    (if i = 0 then NE.cnt else r32 CN i)) 0) 17971200 = true := by quickRfl
theorem k_lab : labK 1755 11 NE.k NE.G (r32 L) = true := by quickRfl
@[expose] noncomputable def kmkF (i : Nat) : Bool :=
  Nat.beq (rg 4096 (mask 4096) MK 0 i) (mkeyK 1755 11 28 11 (r32 MISC 0)
    (fun x => nIf(Nat.blt x 2048, pg 11 (mask 11) (LF 0) x, PEnum.r32 L x)) (REP i))
@[expose] noncomputable def kmkC (c : Nat) : Bool :=
  allN 32 (fun t => bIf(Nat.blt (Nat.add (Nat.mul c 32) t) 457, kmkF (Nat.add (Nat.mul c 32) t),
    true))
#kc_each kmkC 0 15
#kc_forall_chunks kmk_all (fun c => kmkC c = true) 15 CertificateChecks.KernelTitsOver.Three.kmkC 1
theorem k_mk : allN 457 (fun i => Nat.beq (rg 4096 (mask 4096) MK 0 i)
    (mkeyK 1755 11 28 11 (r32 MISC 0) (r32 L) (REP i))) = true := by
  rw [lab_lit]
  exact allN_of_guarded (f := kmkF) (by decide) (by decide) kmk_all
theorem k_mkd : allN 457 (fun i => allN 457 (fun j => bIf(Nat.blt i j,
    bIf(Nat.beq (rg 4096 (mask 4096) MK 0 i) (rg 4096 (mask 4096) MK 0 j), false, true), true))) =
    true := by quickRfl

theorem k_kindA : pairData.kind.all (fun k => Nat.blt k 5) = true := by quickRfl
theorem k_kind : allN 456 (fun i => Nat.blt (pairData.kind[i]!) 5) = true :=
  allN_of_all (p := fun k => Nat.blt k 5) (by decide) k_kindA
@[expose] noncomputable def kindSmF (i k : Nat) : Bool :=
  bIf(Nat.beq k 0, true, bAnd(Nat.blt (r32 SMQ i) (SC (Nat.sub k 1)),
    Nat.beq (ST (Nat.sub k 1) (r32 SMQ i)) (REP (Nat.succ i))))
theorem k_smA : pairData.kind.zipIdx.all (fun p => kindSmF p.2 p.1) = true := by quickRfl
theorem k_sm : allN 456 (fun i => bIf(Nat.beq (pairData.kind[i]!) 0, true,
    bAnd(Nat.blt (r32 SMQ i) (SC (Nat.sub (pairData.kind[i]!) 1)),
      Nat.beq (ST (Nat.sub (pairData.kind[i]!) 1) (r32 SMQ i)) (REP (Nat.succ i))))) = true :=
  allN_of_zipIdx (f := kindSmF) (by decide) k_smA
theorem k_mw : allN 2 (fun k => allN 4 (fun l =>
    bAnd(Nat.blt (r32 MWQ (Nat.add (Nat.mul 4 k) l)) (SC k),
      wordBK 2 6 (r32 CertificateChecks.KernelMaxD2.TitsD.PT) (genLf 11 (mask 11) Dk)
        (genLf 11 (mask 11) DIk) ((memWords.getD k []).getD l [])
        (pg 11 (mask 11) (ST k (r32 MWQ (Nat.add (Nat.mul 4 k) l))))))) = true := by
  rw [dk_eq, dik_eq]
  quickRfl

end CertificateChecks.KernelTitsOver.Three

end
