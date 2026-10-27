module

public import CFSG.Sporadic.Recognition.LyonsFinalModularInputs
public import CFSG.Sporadic.Recognition.LyonsFinalCore107

public section

namespace CertificateChecks.KernelLyBase

open CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] def famKind (eEvs : List EEv) (trEvs : List TrEv) (R : List (List (Fin 6 × Bool))) :
    Bool :=
  R.all fun r => isBWord r || r == kkRel || eEvs.any (fun e => r == eRelOf e) ||
    trEvs.any (fun ev => r == trRel ev)

theorem core_kind : famKind eEvCore trEvCore (Rcore107 ++ modularLearned) = true := by
  decide +kernel

theorem rb_mem_core : ∀ r ∈ RB, r ∈ Rcore107 := by decide +kernel

end CertificateChecks.KernelLyBase

end
