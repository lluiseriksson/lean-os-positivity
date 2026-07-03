# Milestones

## lean-os-positivity — la definición del objetivo.

- M0: definición de reflection positivity en lattice finito (reflexión θ,
  ⟨θF·F⟩ ≥ 0 en un semiespacio). Refs: Osterwalder-Seiler 1978; Glimm-Jaffe cap. 6.
- M1: RP para Ising ferromagnético y cadena gaussiana vía transfer matrix
  (importa lean-transfer-matrix cuando publique su vM1).
- M2: reconstrucción GNS: Hilbert cociente, T contracción autoadjunta positiva,
  H := -log T, enunciado formal "mass gap = gap(H) > 0".
- M3: statements-first de RP para gauge con acción de Wilson.
- Anti-goal: límite continuo, axiomas OS completos en R^d.

## Current Status

- M0: present as compilable definitions in `OSPositivity/ReflectionPositivity.lean`.
- M1: statement/certificate interface only; blocked on published
  `lean-transfer-matrix` vM1.
- M2: statement/data interface only in `OSPositivity/GNS.lean`.
- M3: statement/certificate interface only in `OSPositivity/Wilson.lean`.
