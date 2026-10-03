/-
lean_work/L5_2/NPosProof.lean — L5_2, 28 Sep 2026. **NPos proved from the kernel-replayed cell certificate.**
12 shard files NPosS0..NPosS11 (600 cells, breakpoints A/2^24 covering [0, 30]); each cell theorem is
`MajCheck.cellOk A B = true := by decide +kernel`; soundness `MajSound.chainOk_sound` (MajSoundNPos.lean).
Remaining assumption: node C06 `sinCosPiQ_contains` (statement, L5_1).
-/
import ZetaS.Majorant.MajSoundNPos
import ZetaS.Majorant.Shards.NPosS0
import ZetaS.Majorant.Shards.NPosS1
import ZetaS.Majorant.Shards.NPosS2
import ZetaS.Majorant.Shards.NPosS3
import ZetaS.Majorant.Shards.NPosS4
import ZetaS.Majorant.Shards.NPosS5
import ZetaS.Majorant.Shards.NPosS6
import ZetaS.Majorant.Shards.NPosS7
import ZetaS.Majorant.Shards.NPosS8
import ZetaS.Majorant.Shards.NPosS9
import ZetaS.Majorant.Shards.NPosS10
import ZetaS.Majorant.Shards.NPosS11

open Real

noncomputable section

namespace ZetaS.MajSound

open ZetaS.MCert ZetaS.MajCheck

lemma chain_range (hC : CNodes) {a b : ℕ} {rest : List ℕ} (h : MajCheck.chainOk (a :: b :: rest) = true) (hi : ℕ)
    (hhi : lastD b rest = hi) : ∀ s : ℝ, (a : ℝ) / 2 ^ 24 ≤ s → s ≤ (hi : ℝ) / 2 ^ 24 → 0 ≤ Pmaj s := by
  subst hhi; exact chainOk_sound hC a b rest h

/-- `Q` holds on every sub-interval `[a/2²⁴, b/2²⁴]` of consecutive breakpoints. -/
def pairsHold (Q : ℝ → Prop) : List ℕ → Prop
  | a :: b :: rest => (∀ s : ℝ, (a : ℝ) / 2 ^ 24 ≤ s → s ≤ (b : ℝ) / 2 ^ 24 → Q s) ∧ pairsHold Q (b :: rest)
  | _ => True

theorem cover_of_pairs (Q : ℝ → Prop) : ∀ (a b : ℕ) (rest : List ℕ), pairsHold Q (a :: b :: rest) →
    ∀ s : ℝ, (a : ℝ) / 2 ^ 24 ≤ s → s ≤ (lastD b rest : ℝ) / 2 ^ 24 → Q s
  | a, b, [], h, s, h1, h2 => h.1 s h1 h2
  | a, b, c :: rest, h, s, h1, h2 => by
    rcases le_total s ((b : ℝ) / 2 ^ 24) with hs | hs
    · exact h.1 s h1 hs
    · exact cover_of_pairs Q b c rest h.2 s hs h2

/-- **NPos from the certificate**, given the C-node statements: P(s) ≥ 0 on [0, 30]. -/
theorem npos_of_CNodes (hC : CNodes) : NPos := by
  intro s hs
  have hP : pairsHold (fun s => 0 ≤ Pmaj s) [0, 75497472, 125829120, 168820736, 209715200, 246415360, 286261248, 324009984, 360185856, 395837440, 432013312, 467664896, 503316480] := ⟨
    chain_range hC NPosS0_ok 75497472 rfl,
    chain_range hC NPosS1_ok 125829120 rfl,
    chain_range hC NPosS2_ok 168820736 rfl,
    chain_range hC NPosS3_ok 209715200 rfl,
    chain_range hC NPosS4_ok 246415360 rfl,
    chain_range hC NPosS5_ok 286261248 rfl,
    chain_range hC NPosS6_ok 324009984 rfl,
    chain_range hC NPosS7_ok 360185856 rfl,
    chain_range hC NPosS8_ok 395837440 rfl,
    chain_range hC NPosS9_ok 432013312 rfl,
    chain_range hC NPosS10_ok 467664896 rfl,
    chain_range hC NPosS11_ok 503316480 rfl,
    trivial⟩
  have hl : lastD 75497472 [125829120, 168820736, 209715200, 246415360, 286261248, 324009984, 360185856, 395837440, 432013312, 467664896, 503316480] = 503316480 := rfl
  refine cover_of_pairs (fun s => 0 ≤ Pmaj s) _ _ _ hP s ?_ ?_
  · norm_num; exact hs.1
  · rw [hl]; norm_num; exact hs.2

/-- **NPos, proved** (modulo the statements of nodes C05/C06, via `cnodes_of_statements`). -/
theorem npos_proved : NPos := npos_of_CNodes cnodes_of_statements

end ZetaS.MajSound
