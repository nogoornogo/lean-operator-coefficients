# Fixed-Family Screening Result

The first bounded endpoint derives universal actual-light inclusion for every
Yukawa in the existing scalar multiplet at its fixed vacuum and zero bare
mass. It uses the exhaustive five-coupling image, not a UV character or an
assumption that an index determines the light spectrum.

[LightPlacementObstruction](../../../GUT/SU6/Yukawa/LightPlacementObstruction.lean)
proves `all_yukawas_untouched`: every exterior basis component whose second
index is not 5 lies in the radical of every generated mass. These are the
first-five exterior components (the standard ten). It also proves
`no_exact_light_omitting`: no proposed light subspace omitting any one of
these actual components can be the exact radical of an admitted generated
mass.

Thus a route that tries to remove such a component solely by varying this
family's Yukawa coefficients fails. This does not classify residual actions,
construct a protecting model or extend the scalar/block qque theorem to every
mass. Light inclusion does not itself imply residual invariance, an exact
spectrum or qque neutrality under arbitrary new actions.

## Stop and next scope

The first screen reaches its obstruction endpoint. Escaping this mass-placement
route requires a genuinely different vacuum/scalar family or carrier, or a
residual action outside the prior scalar/block class while retaining the
forced light components. Those alternatives are different model inputs;
none is silently added or asserted to protect B1. Choosing and specifying one
is the next model-level decision, before further proof implementation.

The current prohibition/mixed-request APIs can test supplied candidates but
cannot invent these inputs. Dev–Mohapatra heavy elimination is useful for
specified action matching, not for circumventing this light-placement
obstruction; its unmerged sources are not prerequisites here.
