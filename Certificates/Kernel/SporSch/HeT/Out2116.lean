module

public import Certificates.Kernel.SporSch.HeT.Tab
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.SporSch.PairHeCntSound
public import CFSG.Sporadic.Schreier.PairHeClasses
public import CFSG.Sporadic.HeldB.OuterArithCheckInputs
public meta import CFSG.Sporadic.HeldB.AutData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.HeldB.OuterArithCheckInputs
public meta import CFSG.Sporadic.HeldB.HeBlocks
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.HeAR CFSG.Sporadic.HeldB.heAutRHex

#kmisc_hexflat CertificateChecks.KernelSporSch.HeAR CFSG.Sporadic.HeldB.heAutRHex 4 8330 14 1

namespace CertificateChecks.KernelSporSch.HeO16

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

meta def rM : Array Nat := CFSG.Sporadic.HeldB.heAutRArr

meta def permsM : Array (Array Nat) :=
  #[invCand 8330 rM, CFSG.Sporadic.HeldB.hePowA rM 2]

meta def nfOf (g : Array Nat) : Nat :=
  let nf := decodeNF CFSG.Sporadic.HeldB.heLevels
    ((CFSG.Sporadic.HeldB.heBase.map fun b => g[b]!).toArray)
  (List.range nf.size).foldl (fun acc i => acc ||| (nf[i]! <<< (16 * i))) 0

meta def witOf (g : Array Nat) : Nat :=
  let nf := decodeNF CFSG.Sporadic.HeldB.heLevels
    ((CFSG.Sporadic.HeldB.heBase.map fun b => g[b]!).toArray)
  let wd := nfWord CFSG.Sporadic.HeldB.heLevels nf
  ((List.range 8330).find? fun x => g[x]! != evR wd x).getD 0

meta def natsM : List Nat :=
  [nfOf (CFSG.Sporadic.HeldB.hePowA rM 2), nfOf rM, witOf rM]

end CertificateChecks.KernelSporSch.HeO16

#kss_perms CertificateChecks.KernelSporSch.HeO16P 14 CertificateChecks.KernelSporSch.HeO16.permsM

#knatlist CertificateChecks.KernelSporSch.HeO16.nats CertificateChecks.KernelSporSch.HeO16.natsM

namespace CertificateChecks.KernelSporSch.HeO16

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

@[expose] noncomputable def R : Nat := HeAR.F 0

@[expose] noncomputable def RI : Nat := HeO16P 0

@[expose] noncomputable def R2 : Nat := HeO16P 1

@[expose] noncomputable def F2 : Nat := nats.getD 0 0

@[expose] noncomputable def F1 : Nat := nats.getD 1 0

@[expose] noncomputable def x1 : Nat := nats.getD 2 0

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def pp (p e : Nat) : Nat := ppow 8330 14 (mask 14) (pidn 8330 14) p e

@[expose] noncomputable def W2 : Nat := pp (pc (HeC.S 0) (pp (HeC.S 1) 2)) 2

theorem kInv : invEqK 8330 14 (mask 14) (8330 * 14) R RI = true := by quickRfl
theorem kCanon : canonK 8330 14 (mask 14) (8330 * 14) R = true := by quickRfl
theorem kPow10 : Nat.beq (pp R 10) (pidn 8330 14) = true := by quickRfl
theorem kPow2 : neIdK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) (pp R 2) = true := by quickRfl
theorem kPow5 : neIdK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) (pp R 5) = true := by quickRfl
theorem kComm0 : commK 8330 14 (mask 14) (8330 * 14) R (HeC.S 0) = true := by quickRfl
theorem kComm1 : Nat.beq (pc W2 (pc R (HeC.S 1))) (pc (HeC.S 1) (pc W2 R)) = true := by quickRfl
theorem kR2 : Nat.beq (pp R 2) R2 = true := by quickRfl
theorem kF : bAnd(nfValidK 5 HeC.LR F2, nfValidK 5 HeC.LR F1) = true := by quickRfl
theorem kBase : eqOnL heBase (HeTc.nfp F1) (pg 14 (mask 14) R) = true := by quickRfl
theorem kWit : Bool.not (Nat.beq (pg 14 (mask 14) R x1) (HeTc.nfp F1 x1)) = true := by quickRfl

@[expose] noncomputable def bindB (c : Nat) : Bool :=
  allN 833 (fun j => bind5At 8330 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT F2 R2
    (Nat.add (Nat.mul c 833) j))

theorem kB0 : bindB 0 = true := by quickRfl
theorem kB1 : bindB 1 = true := by quickRfl
theorem kB2 : bindB 2 = true := by quickRfl
theorem kB3 : bindB 3 = true := by quickRfl
theorem kB4 : bindB 4 = true := by quickRfl
theorem kB5 : bindB 5 = true := by quickRfl
theorem kB6 : bindB 6 = true := by quickRfl
theorem kB7 : bindB 7 = true := by quickRfl
theorem kB8 : bindB 8 = true := by quickRfl
theorem kB9 : bindB 9 = true := by quickRfl

theorem idParts : canonK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) = true ∧
    idK 8330 14 (mask 14) = true :=
  (bAnd_iff (canonK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14)) (idK 8330 14 (mask 14))).1
    He2112.idOK

theorem hidc : canonK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) = true := idParts.1

theorem hid : unpack 8330 14 (pidn 8330 14) = idA 8330 := idK_sound idParts.2

theorem canonS (j : Nat) (hj : j < 9) : canonK 8330 14 (mask 14) (8330 * 14) (HeC.S j) = true :=
  ((bAnd_iff (canonK 8330 14 (mask 14) (8330 * 14) (HeC.S j))
    (canonK 8330 14 (mask 14) (8330 * 14) (HeC.SI j))).1 (allN_spec He2112.canonOK j hj)).1

theorem unpackGet {p x : Nat} (hx : x < 8330) : (unpack 8330 14 p)[x]! = pg 14 (mask 14) p x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem pow_unpack {p : Nat} (hp : canonK 8330 14 (mask 14) (8330 * 14) p = true) :
    ∀ e, hePowA (unpack 8330 14 p) e = unpack 8330 14 (pp p e) ∧
      canonK 8330 14 (mask 14) (8330 * 14) (pp p e) = true
  | 0 => ⟨hid.symm, hidc⟩
  | e + 1 => by
    obtain ⟨ih1, ih2⟩ := pow_unpack hp e
    have e1 : pp p (e + 1) = pc p (pp p e) :=
      CFSG.KS.PEnum.strictN_app' (pp p e) (fun q => pcomp 8330 14 (mask 14) p q)
    rw [hePowA, ih1, e1]
    exact ⟨compA_unpack hp ih2, canonK_pcomp hp ih2⟩

theorem gen_eq (l : Nat) (hl : l < 2) : heGen l = unpack 8330 14 (HeC.S l) := by
  have h := He2112.gen_eq l hl
  rw [heGenArrs, getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn] at h
  exact h

theorem R_eq : heAutRArr = unpack 8330 14 R := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound HeAR.all 0 (by norm_num)
  rw [← HeAR.eq] at h
  exact h

noncomputable abbrev E (F : Nat) : Equiv.Perm (Fin 8330) :=
  nfElt 8330 heStrongArrs heBase.toArray (nfArr 5 F)

theorem E_rep {F : Nat} (hF : nfValidK 5 HeC.LR F = true) : RepF 8330 (HeTc.nfp F) (E F) :=
  (nfPtT_sound HeTc.tc hF).2

theorem E_mem {F : Nat} (hF : nfValidK 5 HeC.LR F = true) :
    E F ∈ heChain.originalSubgroup :=
  nfElt_mem heChainArrays (chainCheckFacts heChain_check.1) heChain_valid.1
    (nfPtT_sound HeTc.tc hF).1

theorem rep_of_repF {p : Nat} {g : Equiv.Perm (Fin 8330)} (h : RepF 8330 (pg 14 (mask 14) p) g) :
    Rep 8330 (unpack 8330 14 p) g := fun x => by
  rw [unpackGet x.2]
  exact h x x.2

theorem bind_all : ∀ x < 8330, bind5At 8330 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT F2 R2 x = true := by
  intro x hx
  have hc : ∀ c < 10, bindB c = true := by
    intro c hc
    interval_cases c
    exacts [kB0, kB1, kB2, kB3, kB4, kB5, kB6, kB7, kB8, kB9]
  have h := allN_spec (hc (x / 833) (by omega)) (x % 833) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (x / 833) 833) (x % 833) = x := by
    change x / 833 * 833 + x % 833 = x
    exact Nat.div_add_mod' x 833
  rwa [e] at h

theorem hFs : nfValidK 5 HeC.LR F2 = true ∧ nfValidK 5 HeC.LR F1 = true :=
  (bAnd_iff (nfValidK 5 HeC.LR F2) (nfValidK 5 HeC.LR F1)).1 kF

theorem hF2 : nfValidK 5 HeC.LR F2 = true := hFs.1
theorem hF1 : nfValidK 5 HeC.LR F1 = true := hFs.2

theorem R2_rep : Rep 8330 (unpack 8330 14 R2) (E F2) :=
  rep_of_repF (bind5_spec HeTc.tc hF2 bind_all)

theorem R_rep : Rep 8330 (unpack 8330 14 R) (permOfArr 8330 (unpack 8330 14 R)) :=
  (rep_permOfArr (invEqK_sound kInv).2).1

theorem R_not_mem : permOfArr 8330 (unpack 8330 14 R) ∉ heChain.originalSubgroup := by
  intro hm
  have hR : RepF 8330 (pg 14 (mask 14) R) (permOfArr 8330 (unpack 8330 14 R)) := fun x hx => by
    rw [← unpackGet hx]
    exact R_rep ⟨x, hx⟩
  have he := eq_of_eqOnL he_baseFaithful (E_rep hF1) hR (E_mem hF1) hm kBase
  have hx : x1 < 8330 := by decide
  have h1 := hR x1 hx
  rw [← he, ← E_rep hF1 x1 hx] at h1
  have k := kWit
  rw [h1, Nat.beq_refl] at k
  exact absurd k (by decide)

theorem facts :
    isInvA 8330 heAutRArr (invCand 8330 heAutRArr) = true ∧
    eqA 8330 (hePowA heAutRArr 10) (idA 8330) = true ∧
    eqA 8330 (hePowA heAutRArr 2) (idA 8330) = false ∧
    eqA 8330 (hePowA heAutRArr 5) (idA 8330) = false ∧
    eqA 8330 (compA 8330 heAutRArr (heGen 0)) (compA 8330 (heGen 0) heAutRArr) = true ∧
    eqA 8330 (compA 8330 heW2Arr (compA 8330 heAutRArr (heGen 1)))
      (compA 8330 (heGen 1) (compA 8330 heW2Arr heAutRArr)) = true ∧
    siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0 heAutRArr = false ∧
    siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0
      (hePowA heAutRArr 2) = true := by
  have hS0 := canonS 0 (by norm_num)
  have hS1 := canonS 1 (by norm_num)
  obtain ⟨i1, i2⟩ := invEqK_sound kInv
  have p10 := pow_unpack kCanon 10
  have p2 := pow_unpack kCanon 2
  have p5 := pow_unpack kCanon 5
  have pS1 := pow_unpack hS1 2
  have hA := pow_unpack (canonK_pcomp hS0 pS1.2) 2
  have eW : heW2Arr = unpack 8330 14 W2 := by
    rw [heW2Arr, gen_eq 0 (by norm_num), gen_eq 1 (by norm_num), pS1.1, compA_unpack hS0 pS1.2]
    exact hA.1
  have hW : canonK 8330 14 (mask 14) (8330 * 14) W2 = true := hA.2
  rw [R_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [i1]
    exact i2
  · rw [p10.1, Nat.eq_of_beq_eq_true kPow10, ← hid]
    exact eqK_sound (Nat.beq_refl _)
  · rw [p2.1]
    exact neIdK_sound kPow2
  · rw [p5.1]
    exact neIdK_sound kPow5
  · rw [gen_eq 0 (by norm_num)]
    exact commK_sound kComm0
  · rw [gen_eq 1 (by norm_num), eW, compA_unpack kCanon hS1, compA_unpack hW (canonK_pcomp kCanon hS1),
      compA_unpack hW kCanon, compA_unpack hS1 (canonK_pcomp hW kCanon)]
    exact eqK_sound kComm1
  · rw [Bool.eq_false_iff]
    intro h
    have := (mem_heP_iff_siftA R_rep).1 h
    rw [heP_eq_originalSubgroup] at this
    exact R_not_mem this
  · rw [p2.1, Nat.eq_of_beq_eq_true kR2, mem_heP_iff_siftA R2_rep, heP_eq_originalSubgroup]
    exact E_mem hF2

end CertificateChecks.KernelSporSch.HeO16

end
