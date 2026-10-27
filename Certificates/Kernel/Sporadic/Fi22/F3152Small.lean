module

public import Certificates.Kernel.Sporadic.Fi22.F3152Data
public import Certificates.Kernel.Sporadic.Fi22.F3152Bind
public import Certificates.Kernel.Fi22Core.Data
public import CFSG.Certificates.Kernel.BabyMonster.B64Gen
public import CFSG.Monster.B.Fischer.Fi22SepData
public import Certificates.Data.Kernel.Spor.F3LaneSep

public section

set_option maxRecDepth 400000

#text_pieces CertificateChecks.KernelSpor.F3152.TI CFSG.Monster.B.Fischer.fi22InvFormText "Certificates/Data/CFSGNative/Fi22Pinned/fi22-invariant-form.txt" 752 12021333035395367075 0 752

namespace CertificateChecks.KernelSpor.F3152

open CFSG.KS.F3152 CFSG.KS.F3L CFSG.F3.Native CFSG.Monster.B.Fischer

set_option Elab.async false

@[expose] noncomputable def rowsK (L : V) : List V → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ n => Nat.beq n (nat_lit 0))
    (fun x _ ih i n => bAnd(eqV x (blk (nat_lit 77) L i), ih (Nat.succ i) (Nat.pred n)))

theorem inv_line : bAnd(linesK (fun _ => SL (nat_lit 3510)) (nat_lit 1) TI.CH (nat_lit 0),
    nilK (dropK (nat_lit 1) TI.CH)) = true := by decide +kernel

theorem inv_pull : bAnd(eqV (mulK (SL (nat_lit 3512)) (mulK (SL (nat_lit 3510))
    CertificateChecks.KernelFi22C.LA)) (SL (nat_lit 3510)),
  eqV (mulK (SL (nat_lit 3513)) (mulK (SL (nat_lit 3510)) CertificateChecks.KernelFi22C.LB))
    (SL (nat_lit 3510))) = true := by decide +kernel

theorem bi_rows : rowsK (SL (nat_lit 3511)) fi22Bi.toList (nat_lit 0) (nat_lit 77) = true := by
  decide +kernel

theorem bi_id : bAnd(eqV (mulK (SL (nat_lit 3510)) (SL (nat_lit 3511))) ⟨dgK, nat_lit 0⟩,
    eqV ⟨dgK, nat_lit 0⟩ CertificateChecks.KernelFi22C.LI) = true := by decide +kernel

theorem tr_ok : bAnd(eqV (trLane (nat_lit 77) CertificateChecks.KernelFi22C.LA) (SL (nat_lit 3512)),
    eqV (trLane (nat_lit 77) CertificateChecks.KernelFi22C.LB) (SL (nat_lit 3513))) = true := by
  decide +kernel

theorem tail_ok : nilK (dropK (nat_lit 3510) T.CH) = true := by decide +kernel

theorem sorted_ok : sortedK (msortK (T.CH.map Prod.fst)) = true := by decide +kernel

end CertificateChecks.KernelSpor.F3152

end
