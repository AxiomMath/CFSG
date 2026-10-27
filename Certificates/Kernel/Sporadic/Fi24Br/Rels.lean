
module

public import Certificates.Kernel.VecCert.HomBound3
public import Certificates.Kernel.VecCert.WordProg
public import Certificates.Kernel.Sporadic.Fi24Br.Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyFour
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Certificates.Kernel.Orders.Fi24p.Rels
import Certificates.Kernel.Sporadic.Fi24Br.K
import Certificates.Kernel.Sporadic.Fi24Br.S0
import Certificates.Kernel.Sporadic.Fi24Br.S1
import Certificates.Kernel.Sporadic.Fi24Br.R0
import Certificates.Kernel.Sporadic.Fi24Br.R1
import Certificates.Kernel.Sporadic.Fi24Br.R2
import Certificates.Kernel.Sporadic.Fi24Br.D
import Certificates.Kernel.Sporadic.Fi24Br.Seed
import Certificates.Kernel.Sporadic.Fi24Br.Light
import CFSG.Certificates.Kernel.Orders.Fi24p.RelsBind
import CFSG.Certificates.Kernel.Spor.Dec3Sound
import CFSG.Certificates.Kernel.Spor.BytesFSound
import CFSG.Sporadic.Fi24.SetupBase
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.ForallChunks
import Mathlib.Tactic.IntervalCases
import Certificates.Kernel.Sporadic.BrChain
public import Certificates.Kernel.Sporadic.Fi24Br.Prog
import CFSG.Blueprint.MatrixSeedIdentification
import CFSG.Certificates.SchreierStabilizerGenerators
import CFSG.Sporadic.Fi24.CertificateBase

public section

set_option maxRecDepth 400000

namespace CFSG.KD.BrFi24

#kc_forall_chunks IV.all (fun g => ivC g = true) 11 CFSG.KD.BrFi24.ivC 1
#kc_forall_chunks S.all (fun k => sC k = true) 13 CFSG.KD.BrFi24.sC 1
#kc_forall_chunks R.all (fun j => rC j = true) 70 CFSG.KD.BrFi24.rC 1

end CFSG.KD.BrFi24

namespace CertificateChecks.KernelSpor.Fi24Rels

open CFSG.KC.Ord CFSG.KC.WP CFSG.KD.BrFi24 CFSG.KS.Mat3 CertificateChecks.KernelHomG
  CertificateChecks.KernelHom3 CertificateChecks.KernelWP

theorem hs : LayoutSound (Canon3 609961) (mat3 781 609961) MUL VLD ONE := layout3 consts

theorem hroot : rootsOK RB VLD 1 (11 + 1) = true := hroots

theorem recAnd {f : Nat → Bool} : ∀ n, (∀ g < n, f g = true) →
    Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) n = true
  | 0, _ => rfl
  | n + 1, h => by
    change andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) n) (f n) = true
    rw [recAnd n (fun g hg => h g (by omega)), h n (by omega)]
    rfl

theorem invsOK_of {RB' : Nat → Nat} {mul : Nat → Nat → Nat} {vld : Nat → Bool} {L ONE' : Nat}
    (h : ∀ g < L, andB (vld (RB' (Nat.add (Nat.succ L) g)))
      (Nat.beq (mul (RB' (Nat.succ g)) (RB' (Nat.add (Nat.succ L) g))) ONE') = true) :
    invsOK RB' mul vld L ONE' = true :=
  recAnd L h

theorem all11 {p : Nat → Prop} (h0 : p (nat_lit 0)) (h1 : p (nat_lit 1)) (h2 : p (nat_lit 2))
    (h3 : p (nat_lit 3)) (h4 : p (nat_lit 4)) (h5 : p (nat_lit 5)) (h6 : p (nat_lit 6))
    (h7 : p (nat_lit 7)) (h8 : p (nat_lit 8)) (h9 : p (nat_lit 9)) (h10 : p (nat_lit 10)) :
    ∀ g < 11, p g := by
  intro g hg
  interval_cases g
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

theorem hinv : invsOK RB MUL VLD (nat_lit 11) ONE = true :=
  invsOK_of CFSG.KD.BrFi24.IV.all

theorem hS : ∀ k < 13, progOK RB 11 RS MUL ONE (PS k) (RS k) = true :=
  CFSG.KD.BrFi24.S.all

theorem goodS : ∀ k < 13, Good (Canon3 609961) (mat3 781 609961) RB 11 (RS k) (WC k) :=
  states_good hs hroot hinv statesL hS

theorem hR : ∀ j < 70, progOK RB 11 RS MUL ONE (PR j) ONE = true :=
  CFSG.KD.BrFi24.R.all

theorem hrel : ∀ v ∈ CFSG.KD.OrdFi24p.rels,
    (v.map fun x => mat3 781 609961 (letM RB 11 x)).prod = 1 :=
  rels_of_cover hs hroot hinv relB (relProgs_one hs hroot hinv goodS relsL hR)
    (by rw [relLen]; exact coverL)

theorem hregs : RegsInG (Canon3 609961) (mat3 781 609961) 11 RB 25 := by
  refine regsIn_of hs hroot hinv fun r h1 h2 => ?_
  have hA := statesOK_spec 13 statesL 0 (by decide)
  have hB := statesOK_spec 13 statesL 12 (by decide)
  have e : r = 23 ∨ r = 24 := by omega
  rcases e with rfl | rfl
  · exact ⟨WC 0, goodS 0 (by decide), hA.2.2.2⟩
  · exact ⟨WC 12, goodS 12 (by decide), hB.2.2.2⟩

theorem seed3_sound1 {d f N LO RM CI ONE UP lb len M St : Nat} {F : Nat → Nat}
    {cs : List Char} {Cs : List Nat}
    (hr : Nat.beq (decRun3 F lb len d N RM M Cs (nat_lit 1)) St = true)
    (hd : seedDone d (valid3 N LO) M St = true)
    (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hb : CFSG.KS.Bytes.bytesEqK cs F lb len = true)
    (hCs : Cs = List.range ((len + lb - 1) / lb)) :
    CFSG.Blueprint.NativeSporadic.decode 3 d 1 (String.ofList cs) = mat3 d N M :=
  CFSG.KS.Dec3.seed3_sound hc hb hCs hr hd

theorem mA_eq : CFSG.Blueprint.NativeSporadic.decode 3 781 1
    CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 = mat3 781 609961 (RB 23) := by
  have hr := BrChain.run_chain_to (run := decRun3 P1 256 617792 781 609961 RM (RB 23)) (fun _ => rfl)
      (fun l₁ l₂ s => CFSG.KS.Dec3.decRun3_append _ _ _ _ _ _ _ l₁ l₂ s) dL (fun k => DA1.getD k 0) 10
      (nat_lit 1) (nat_lit 2439847) rfl rfl D1.all
  have h := seed3_sound1 hr d1_end consts (CFSG.KS.Bytes.bytesEqK_of_runF (by decide) seed1_run)
    (by decide +kernel)
  rw [← CFSG.Sporadic.Fi24.seedA_eq, SA.eq, h]

theorem mB_eq : CFSG.Blueprint.NativeSporadic.decode 3 781 1
    CFSG.Blueprint.NativeSporadic.Fi24primeSeed2 = mat3 781 609961 (RB 24) := by
  have hr := BrChain.run_chain_to (run := decRun3 P2 256 617792 781 609961 RM (RB 24)) (fun _ => rfl)
      (fun l₁ l₂ s => CFSG.KS.Dec3.decRun3_append _ _ _ _ _ _ _ l₁ l₂ s) dL (fun k => DA2.getD k 0) 10
      (nat_lit 1) (nat_lit 2439847) rfl rfl D2.all
  have h := seed3_sound1 hr d2_end consts (CFSG.KS.Bytes.bytesEqK_of_runF (by decide) seed2_run)
    (by decide +kernel)
  rw [← CFSG.Sporadic.Fi24.seedB_eq, SB.eq, h]

theorem gens_eq : TauCeti.Sporadic.fi24PrimePresentation.generatorCount = 11 := by
  simp [TauCeti.GroupPresentation.generatorCount,
    TauCeti.Sporadic.fi24PrimePresentation_generatorNames]

theorem le_range : ∃ φ : TauCeti.Sporadic.fi24PrimePresentation.Group →* GL (Fin 781) (ZMod 3),
    ∀ g : GL (Fin 781) (ZMod 3),
      g.val = CFSG.Blueprint.NativeSporadic.decode 3 781 1
          CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 ∨
        g.val = CFSG.Blueprint.NativeSporadic.decode 3 781 1
          CFSG.Blueprint.NativeSporadic.Fi24primeSeed2 → g ∈ φ.range :=
  le_range_of_homG _ hs CFSG.KD.OrdFi24p.rels_eq gens_eq hroot hinv relB hrel hregs
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) mA_eq mB_eq

end CertificateChecks.KernelSpor.Fi24Rels

end
