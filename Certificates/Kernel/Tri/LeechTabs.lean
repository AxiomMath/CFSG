module

public import CFSG.Certificates.Kernel.Tri.LeechKSound
public meta import CFSG.Monster.Tri.LeechLongData
public meta import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLeech.Nb CFSG.Monster.Tri.Leech.leechNbrHex
#kmisc_hexflat CertificateChecks.KernelLeech.Nb CFSG.Monster.Tri.Leech.leechNbrHex 6 200 24 23
#ks_chars CertificateChecks.KernelLeech.NP CFSG.Monster.Tri.Leech.leechNbrParHex
#kmisc_hexflat CertificateChecks.KernelLeech.NP CFSG.Monster.Tri.Leech.leechNbrParHex 4 200 16 23
#ks_chars CertificateChecks.KernelLeech.NL CFSG.Monster.Tri.Leech.leechNbrLevHex
#kmisc_hexflat CertificateChecks.KernelLeech.NL CFSG.Monster.Tri.Leech.leechNbrLevHex 1 200 4 23
#ks_chars CertificateChecks.KernelLeech.LP CFSG.Monster.Tri.Leech.leechLongParHex
#kmisc_hexflat CertificateChecks.KernelLeech.LP CFSG.Monster.Tri.Leech.leechLongParHex 4 200 16 23
#ks_chars CertificateChecks.KernelLeech.LL CFSG.Monster.Tri.Leech.leechLongLevHex
#kmisc_hexflat CertificateChecks.KernelLeech.LL CFSG.Monster.Tri.Leech.leechLongLevHex 1 200 4 23

public section

namespace CertificateChecks.KernelLeech

open CFSG.KC.Enum CFSG.KC.Leech CFSG.Monster.Tri.Leech

@[expose] noncomputable def ent (w : Nat) (F : Nat → Nat) (i : Nat) : Nat :=
  pg w (CFSG.KS.mask w) (F (Nat.div i (nat_lit 200))) (Nat.mod i (nat_lit 200))

@[expose] noncomputable def NB : Nat → Nat := ent 24 Nb.F
@[expose] noncomputable def NBP : Nat → Nat := ent 16 NP.F
@[expose] noncomputable def NBL : Nat → Nat := ent 4 NL.F
@[expose] noncomputable def LGP : Nat → Nat := ent 16 LP.F
@[expose] noncomputable def LGL : Nat → Nat := ent 4 LL.F

theorem lens : Nat.beq (CFSG.KS.Len.lenK Nb.chars) 27600 = true ∧
    Nat.beq (CFSG.KS.Len.lenK NP.chars) 18400 = true ∧
    Nat.beq (CFSG.KS.Len.lenK NL.chars) 4600 = true ∧
    Nat.beq (CFSG.KS.Len.lenK LP.chars) 18400 = true ∧
    Nat.beq (CFSG.KS.Len.lenK LL.chars) 4600 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem asciis : CFSG.KS.Text.asciiK Nb.chars = true ∧ CFSG.KS.Text.asciiK NP.chars = true ∧
    CFSG.KS.Text.asciiK NL.chars = true ∧ CFSG.KS.Text.asciiK LP.chars = true ∧
    CFSG.KS.Text.asciiK LL.chars = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem bind_of {s : String} {cs : List Char} {d w : Nat} {F : Nat → Nat} (e : s = String.ofList cs)
    (h : CFSG.KC.Misc.HexFlat.hexFlat cs d 200 w 23 F = true)
    (hl : Nat.beq (CFSG.KS.Len.lenK cs) (d * (200 * 23)) = true)
    (ha : CFSG.KS.Text.asciiK cs = true) :
    (hexTable d s).size = 4600 ∧ ∀ i < 4600, (hexTable d s)[i]! = ent w F i := by
  rw [e]
  exact hexTable_bind h (Nat.eq_of_beq_eq_true hl) ha

theorem of_blocks {f : Nat → Bool} (h : ∀ k < 20, allFrom (230 * k) 230 f = true) :
    CFSG.KLie.CT.allN 4600 f = true := by
  refine (allN_true _ _).2 fun i hi => ?_
  have := h (i / 230) (by omega)
  exact allFrom_true this i (by have := Nat.div_mul_le_self i 230; rw [Nat.mul_comm]; omega)
    (by have := Nat.lt_div_mul_add (a := i) (b := 230) (by decide); rw [Nat.mul_comm]; omega)

theorem nbr_bind : leechNbr.size = 4600 ∧ ∀ i < 4600, leechNbr[i]! = NB i :=
  bind_of Nb.eq Nb.all lens.1 asciis.1

theorem nbrPar_bind : leechNbrPar.size = 4600 ∧ ∀ i < 4600, leechNbrPar[i]! = NBP i :=
  bind_of NP.eq NP.all lens.2.1 asciis.2.1

theorem nbrLev_bind : leechNbrLev.size = 4600 ∧ ∀ i < 4600, leechNbrLev[i]! = NBL i :=
  bind_of NL.eq NL.all lens.2.2.1 asciis.2.2.1

theorem longPar_bind : leechLongPar.size = 4600 ∧ ∀ i < 4600, leechLongPar[i]! = LGP i :=
  bind_of LP.eq LP.all lens.2.2.2.1 asciis.2.2.2.1

theorem longLev_bind : leechLongLev.size = 4600 ∧ ∀ i < 4600, leechLongLev[i]! = LGL i :=
  bind_of LL.eq LL.all lens.2.2.2.2 asciis.2.2.2.2

end CertificateChecks.KernelLeech

end
