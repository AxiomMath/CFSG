module
public import CFSG.Sporadic.HNSchreier.ArchiveGiantData
public import CFSG.Sporadic.HNSchreier.EmbeddedOrbitAccess
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PackedOrbitChecks
public meta import CFSG.Sporadic.HNSchreier.ArchiveGiantData
public meta import CFSG.Sporadic.HNSchreier.EmbeddedOrbitAccess
public meta import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PackedOrbitChecks
public meta import Lean.Elab.Tactic

public meta section
open Lean Elab Tactic Meta
open CFSG.Sporadic.HNSchreier.Native

register_option cfsg.hn2095.chunkSize : Nat := {
  defValue := 512
  descr := "Maximum number of packed orbit rows checked by each independent kernel proof."
}

register_option cfsg.hn2095.masked : Bool := {
  defValue := false
  descr := "Set by Certificate2095; read by no tactic."
}

register_option cfsg.hn2095.window : Bool := {
  defValue := false
  descr := "Set by Certificate2095; read by no tactic."
}

private partial def treeChunks (chunk start count : Nat) : TacticM Unit := withMainContext do
  if count > chunk then
    let target ← instantiateMVars (← getMainTarget)
    let lhs := target.getArg! 1
    unless lhs.isAppOfArity ``Kernel.orbitTreeCheck 4 do
      throwError "expected packed tree comparison"
    let a ← whnf (lhs.getArg! 2)
    unless a.isAppOfArity ``OrbitNats.branch 3 do
      throwError "packed leaf exceeds chunk size"
    let .lit (.natVal leftSize) := (← whnf (a.getArg! 0)) |
      throwError "nonliteral subtree size"
    unless 0 < leftSize && leftSize < count do throwError "invalid subtree split"
    evalTactic (← `(tactic| apply (Kernel.orbitTreeCheck_branch _ _ _ _ _ _ _ _).2))
    evalTactic (← `(tactic| refine ⟨by decide +kernel, ?_, ?_⟩))
    let goals ← getGoals
    unless goals.length == 2 do throwError "expected two subtree goals"
    setGoals [goals[0]!]
    treeChunks chunk start leftSize
    setGoals [goals[1]!]
    treeChunks chunk (start+leftSize) (count-leftSize)
    setGoals []
  else
    let started ← IO.monoMsNow
    evalTactic (← `(tactic| decide +kernel))
    if let some file ← IO.getEnv "CFSG_KERNEL_PROGRESS" then
      IO.FS.writeFile file s!"Checked packed orbit subtree [{start}, {start+count}) in {(← IO.monoMsNow)-started}ms\n"

elab "hn_archive_tree_certificate" : tactic => do
  if let some file ← IO.getEnv "CFSG_KERNEL_STAGE" then
    IO.FS.writeFile file "Started Certificate2095 combined packed-tree check\n"
  evalTactic (← `(tactic| rw [arraysPayload_decode, archiveGiantBytes_toByteArray,
    Kernel.archDataChecks_kernel, Kernel.archEqChecks_kernel]))
  evalTactic (← `(tactic| unfold archiveGiantBytes))
  evalTactic (← `(tactic| rw [Kernel.archDataChecks_packed, Kernel.archEqChecks_packed,
    Kernel.archDataChecks_masked, Kernel.archEqChecks_masked]))
  evalTactic (← `(tactic| unfold Kernel.archEqChecksMasked))
  evalTactic (← `(tactic| simp only [hnsData_orbit, hnsOrbit_alpha_ap, hnsOrbit_beta_ap]))
  evalTactic (← `(tactic| refine Kernel.orbitTreeCheck_certificate _ _
    hnsOrbit_alpha_valid hnsOrbit_beta_valid _ _ rfl (by decide +kernel)
    (by decide +kernel) ?_))
  let chunk := cfsg.hn2095.chunkSize.get (← getOptions)
  if chunk == 0 then throwError "chunk size must be positive"
  treeChunks chunk 0 1140000
  if let some file ← IO.getEnv "CFSG_KERNEL_STAGE" then
    IO.FS.writeFile file "Completed Certificate2095 combined packed-tree check\n"

end
