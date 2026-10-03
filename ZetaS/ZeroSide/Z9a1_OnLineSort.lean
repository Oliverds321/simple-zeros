/-
Sub-node Z9a1 (agent L3_1) — the on-line zeros of a window, sorted by ordinate: a finite set S of points on
Re ρ = ½ is enumerated by a strictly increasing γ : Fin #S → ℝ with ρ_i = ½ + iγ_i (distinct on-line zeros have
distinct ordinates). Feeds `ZeroFrame.x_mono` (x_i = γ_i L/2π) and the reindexing Σ_i f(ρ_i) = Σ_{ρ∈S} f(ρ).
-/
import ZetaS.InterfacesV2

noncomputable section

namespace ZetaS
namespace Z9

theorem onLine_enum (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ.re = 1 / 2) :
    ∃ γ : Fin S.card → ℝ, StrictMono γ ∧
      ∃ e : Fin S.card ≃ S, ∀ i, (e i : ℂ) = (1 / 2 : ℂ) + (γ i : ℂ) * Complex.I := by
  classical
  have hinj : Set.InjOn Complex.im S := by
    intro a ha b hb hab
    apply Complex.ext
    · rw [hS a ha, hS b hb]
    · exact hab
  have hcard : (S.image Complex.im).card = S.card := Finset.card_image_of_injOn hinj
  set γ : Fin S.card → ℝ := fun i => (S.image Complex.im).orderEmbOfFin hcard i with hγ
  have hmem : ∀ i, ((1 / 2 : ℂ) + (γ i : ℂ) * Complex.I) ∈ S := by
    intro i
    have h := (S.image Complex.im).orderEmbOfFin_mem hcard i
    obtain ⟨ρ, hρ, hρi⟩ := Finset.mem_image.mp h
    have : ρ = (1 / 2 : ℂ) + (γ i : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [hS ρ hρ]
      · simp [hγ, hρi]
    rw [← this]; exact hρ
  have hsm : StrictMono γ := ((S.image Complex.im).orderEmbOfFin hcard).strictMono
  refine ⟨γ, hsm, ?_⟩
  let f : Fin S.card → S := fun i => ⟨_, hmem i⟩
  have hf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i j hij => hsm.injective ?_, by simp⟩
    have := congrArg (fun z : S => (z : ℂ).im) hij
    simpa [f] using this
  exact ⟨Equiv.ofBijective f hf, fun i => rfl⟩

end Z9
end ZetaS
