# 1-phase-6: the light-cone sky and the observable meridian

Single-file interactive visualisation: `index.html`. No dependencies.
External verification: `verify-233.js` (84 checks: the pair dynamics,
the events, the oriented octant bridge, the precession theorem, the
mass--energy channel: sign on the base, quarter core on the spinor
cover, the quarter of norm minus one),
`verify-sky.js` (28 checks: the sky map, the fibered covers, the
radial ladder with the tau+2 completion as sets, and the central
product proven as an isomorphism: phi(a, b) = 13a + 12b mod 312
with kernel exactly the identified sign pair), `verify-space.js`
(25 checks: the register, the cone arithmetic, the frame counts,
the permutation spectrum with its spectral generator: H_wind
chi_k = k chi_k and P_g = zeta_12^{-H_wind}, the energy of a mode
its winding rate -- H_wind distinct from the Cayley kinetic
H_kin = 2I - T - T^{-1} of verify-f13 -- and the curl algebra:
delta_k = 78^k a homomorphism on the declared C232 chart, landing
on the cardinals, delta_58 = h),
`verify-f13.js` (25 checks: the shell operator core of [2] -- H^7 =
0, ord(U) = 13, U exactly unitary), `verify-hopf.js` (10 checks: the finite Hopf fibration -- the free
boost action, the unique factorization, the global section, the
horizon-circle fiber coordinate, at p = 13 and Omega-blind at p = 5,
with the SL2 spin contrast and the Cayley station theorem: phi
bijects P1 onto the norm-one C14, origin to 1, horizon class [1:0]
to -1), and `verify-render.js` (20 checks: the
production rendering itself -- the pair sweep over both sky
representations, the caption-free canvases, the label laws, the
double-cover closures in the Carrier view, the drive-hiding of the
Subject view, the wrap continuity in both views, the Hopf lighting
laws, the primitive-arc fiber rendering, the section test: nodes
and labels identical across the toggle, the single-stroke helix
guide loops, the frame leak: standing Carrier chart, the
quarter turn in S chronons, the q hand riding to h, the
one drive sense across the panels: the Carrier-view sky steps
clockwise with the drive, as the shell and the chart, and the
interpolated mode: exact endpoints, +1 quarter class per chronon,
on-tick data, the frame dilation in the sheet-fair chart:
bead-on-fiber, the congruent parity image wF = -w at the half, the
dual's radial band at the quarter, home at the cycle, the ensemble
breathing without collapse, the Subject-view curl present, static,
and Carrier-tick invariant, the spinor half-turn: the sheet flip is
the exact axial pi-rotation, not the spatial antipode, and the
production clock: 696 stepChronon calls land the flipped sheet and
the exact half-turn, 1392 the full home);
node, all passing, all integer arithmetic in the exact suites;
`node run-all.js` runs the six suites and exits nonzero on any
failure. The screen projection is
a labelled chart approximation; every state shown is exact and
discrete. The instance is the minimal non-trivial pair (13, 233),
kappa = 3, Objectless.

## What it shows

The drive x -> gx as the shell's exact unitary evolution -- the
Schrodinger evolution of the windings [3], with its unitary and
spinor structure from [2] -- read through three complementary
square panels of one state, at one scale, under one Subject/Carrier
toggle.

The headline symbol psi is the register itself: the wave function
is phase, each pure mode a power map u -> u^k of the residues [3].
The step g psi therefore carries three exact readings, two of
which the lab draws as its two views: the permutation
P_g|a> = |ga> (Carrier view: the slots turn), the pointwise value
walk (Subject view: every registered value multiplies by g), and
the mode chart, phase g^{-k} per chronon on the winding-k
character. The first two coincide because the values are residue
powers -- multiplying a value by g is shifting a slot by one --
and the label-law checks of verify-render pin both. An amplitude
layer over the residues, with free coefficients, arrives only with
an Object [3]. The panels:

The symmetry shell: the F13 arithmetic symmetry sphere -- meridians,
latitudes, the rotating frame, and the register comb on the frame's
great circle, each cell showing its whole value through the phase
arrow i^r and the rung tint s.

The phase chart: the Carrier ring of 232 ticks, the standing
backdrop of both views; the L1 time latitude with the time-domain
comb, and the shared fold clock r = tau mod 4 with the unit's
lift as its hand; the Subject ring precessing with the Carrier
count under the q/p dial -- the frame leak (00:C17, 00:C18).

The sky: kappa = 3 nested fibers on the radial ladder at the axial
radii R sin(2a pi/p), the Observer at the center; each shell the
complete double-helix fiber -- twelve cells by two routes on one
smooth closed loop through both poles, the sign of -1 distributed
over the orbit; consecutive fibers one rung apart, x3 = g^4, mounted
120 degrees apart about the main axis; 3 x 48 + 12 = 156 = p(p-1),
the totality of the observable (00:Y3).

## The Hopf representation (00:C19, 00:Y3, 00:Y4)

The sky panel carries a representation toggle with three modes:
Drive orbits / Light cone / Hopf fibers. The three representations
share one sky: the same node computation, the same marks, the same
labels -- the toggle switches the fibers and only the fibers. The
drive-orbit mode draws the orbits of x -> gx (the time factor, the
helices -- the retarded stitching of the time histories, per the
arrival reading); the light-cone mode draws the OBSERVABLE SECTOR:
one Dirac flow shared by every mode -- each registered row carries
the retarded flow phi(k) = PHI + k CURL (the Subject view its
gauge-free curl, static and closing with the register; the Carrier
view the frame's common flow) -- while the Subject's own locus is
the frame origin, never dressed: every arc anchors at the drawn
Observer at every clock state; over the full node field ride the
twelve exact stations (the nodes are their own marks), the
capacity folds, M0 solid and the M9 dual (the oriented face of
the +-i line, 5 = g^9 = -g^3) at half strength; the clock bead
displays the frame phase; the Hopf mode draws
the fiber orbits (the boost factor) as a global structure -- the
three cyclic sectors of the frame group as the three fiber layers
over one node set. The chart: the guard
projection (center at w0 = 1.1 outside S3) maps the whole S3 onto
the ball whose silhouette is the horizon sphere, so the sky ball is
a chart of the whole S3 (00:Y4). The chart is two-sheeted -- the
ray through a sky point meets S3 twice -- and the node's spinor
sheet selects the preimage. Each node lifts to its S3 preimage and
carries the exact Hopf circle through it, the leaf of the global
foliation e^{it}(z1, z2), projected back as one closed curve
through the node, node-on-fiber exact. The lift rides the far sheet
-- one fixed chart convention, so the foliation's axial symmetry
makes the leaves rotate rigidly with the nodes (coherence residual
1e-15). The rung ladder is the foliation depth: the three copies of
one event lift to three nested leaves, the inner rung riding the
horizon-circle level (|z2| = 0.14 at the equator), the mid rung at
0.69, the outer rung deep at 0.86 -- the radial ladder of the sky
read as the depth of the S3 foliation, the holographic statement of
00:Y4 made visible. The fiber layer is kept bare and rides the
helix guide style at half strength (the leaves are denser than the
loops): guide grey #8a877f, each leaf split at the two antipodal
roots of its homogeneous depth numerator into one front arc (alpha
0.35) and one back arc (0.12), both primitive elliptical arcs; the
node is the leaf's only marked point (the section point),
identity stays on the node layer. Shown are the 24 outer-rung
leaves, the inner-rung leaves hidden behind the SHOW_INNER flag.
A per-fiber color coding, if ever wanted, keys on the address: the
two routes of one cell share a hue -- the echo pair (00:C7) -- as
a selective-highlight mode, not a full palette. The nodes are the section of the finite fibration PGL2/C14
(00:C19); motion along a fiber is a boost, it changes the observer,
and is unobservable -- observation is the Hopf section (00:Y3). The
13 marks on the outer fibers are the C14 boost points, the node the
fourteenth: the fiber coordinate runs over the projective line, the
thirteen cells plus the horizon class [1:0] -- the frame's own
registration direction, fixed by every translation. Its finite
identity is exact in every chart: additively it is the sign seam of
the exact half, between -1/2 = (p-1)/2 = 6 and +1/2 = (p+1)/2 = 7
(the 1-algebra half theorem; at Carrier scale between 116 = dlog(-1)
and 117, the pair's half event); multiplicatively it is the
half-turn, Cayley-registered as -1. The observer lifts to the pole (0, +-i), the degenerate
leaf: the clock fiber (tau, 0) is the polar axis segment, the
stabilizer, the pure drive. The screen map per leaf is projective
in the circle parameter, so every leaf is an exact ellipse, in
closed form from the conic C = M^-T diag(1,1,-1) M^-1 and drawn as
primitive elliptical arcs: 48 strokes per frame (front and back per
leaf), no fiber polylines, node-on-ellipse to 1e-6 px over the full
state sweep. The
section test in verify-render.js renders a paused state in both
representations and checks every node dot and every label
identical; the combinatorics is carried by verify-hopf.js. The
guard chart is the labelled approximation; the silhouette radius
206 clears the outer shell (node radius 200.5) with margin.

## The frame dilation (00:Y5)

The leak per chronon is an element of the frame group, and by C19
it factors uniquely into a Borel part and a boost part. The Borel
part is the azimuthal drift the panels already draw. The boost part
is motion along the Hopf fiber: the frame dilation, the mass phase
of 00:Y5 -- the boost torus is the Dirac layer's exclusive mass
channel [2], and the mass sector's standard-model interaction face
is [5]. The observability is relational, per the quotient
structure: a pure boost is
unobservable at the quotient (00:Y3), so the COMMON fiber flow is gauge and draws
only in the harness view, as the Carrier-referenced chart
realization anchored at the exact C4 stations. The Subject's
observable is the relative fiber displacement between base points
-- two sections, sS(x) = sC(x) Delta(x), the observable Delta --
and the retardation supplies its exact form: the image at lookback
k lags the common flow by k tick-angles, the boost-curl of 00:C18
(one Carrier tick-angle per chronon of lookback into the boost
direction). The displacement is the group element delta_k = u_C^k
with u_C = 78 the boost unit: a homomorphism in k, primitive of
order 232, delta_58 = h -- and the drawn angle is its chart,
Delta_k = chart(delta_k) = k pi/116 (the curl-algebra check in
verify-space). The Subject view draws this
static, integer-exact, gauge-free curl: the gravitational face of
the Objectless lab, gravitation as phase synchronisation [4], the
apsidal reading of 00:Y2. The curl is drawn as the difference it
is: a faint cyan arc along each outer node's leaf from the
unflowed base to the curled bead, in both representations -- the
frozen precession field, growing with lookback. Time-VARYING
dilation is relational
between systems of different rates -- Mercury needs the Sun -- and
arrives with the first Object. The rate is
forced by the dial: the flip is x h per Carrier quarter, so the
flow runs at the dial's full tick-angle per chronon, prograde, phi
= -(bC + F) pi/116, interpolation-ready and closing exactly at the
Carrier wrap with no sheet bit. The realisation is the pure fiber
flow rendered in the sheet-fair chart: each point projects from
the guard on its own side of S3 (denominator W0 - |q4|), so the
antipodal map is the ball's exact point reflection and no chart
constant enters any station. Every bead rides its own leaf at
every phase -- bead-on-fiber always -- and the helix guide loops
flow pointwise into smooth screwed curves, the pole crossings
passing the center along the observer's axis leaf, as they must.
Stations, exact and gauge-free: at the Carrier quarter the sharp
shell disperses into a radial band, the Fourier dual's spread
(the dual has the units of the inverse: localized to dispersed);
at the half the pattern reassembles as the congruent parity image,
wF = -w exactly at full scale; home with the Carrier cycle, the
pattern with the pair at 696 (the joint return, a proxy-chart
datum: S = 58 Subject-cycles out, registered by the declaring
chart; the pair itself registers the monotone dephasing). The
chart radius along a leaf is
bounded below by the flow-invariant |z1|, so the ensemble breathes
and never collapses. The leaves keep the established closed-ellipse
rendering at the release density in both views. Each event's drawn
fiber is the foliation leaf through its CURRENT bead (the ball
carries the standing chart foliation; re-lifting the flowed
position selects the leaf): the nodes precess along the fibers at
machine precision through the whole cycle, and the fiber family
precesses with them -- at the half the entire fibration stands as
its congruent parity image. The mid-sphere (the q4 = 0 great
sphere, chart radius S3H/W0) is the seam where the atlas's two
projective charts glue, C0 but not C1, so flowed curves bend
exactly there -- the declared signature of the two-chart atlas,
kept in preference to a smoothing gauge that would cost the
conic-exact rendering; the seam is left undrawn.
The visibility profiles follow the flowed positions, in sync with
the guide loops' front/back passes. The clock bead rides
the axis leaf: the Subject's own dilation. The rung-ladder
exchange stays as the discrete arithmetic face of the same
inversion; with the exact per-tick boost step (which C14 element,
via the octant bridge) it is the open derivation that would also
promote 00:Y5 -- now closed (00:Y5, theorem). The winding cycle
meets the boost torus in the sign alone (gcd(232, 14) = 2) and its
spinor cover in exactly the quarter core Q4 (gcd(232, 28) = 4;
universally gcd(p-1, 2(p+1)) = 4 for every p = 4kappa+1): the
per-tick boost step is the Q4 class of the winding rate, carried
on the cover. The quarter is spinorial -- i^2 = -1 gives
N(i) = -1, norm minus one -- so the transport crosses the sheet,
and the sheet-dependent stations draw exactly this. The kill test
at (53, 13) in Carrier 157 passed: the Object drive factors
canonically over C12 = Q4 x C3 into core quarter times outcome,
the winding exponent projects to the same quarter (117 x 13 = 117
mod 156, gen^117 = 28, the published core of [3]), and mass phase
= winding rate as one Q4 datum (ledger validation check_y5).
The C4 station face is homomorphic (gcd(232, 4) = 4):
the quarter, parity, and home stations are group-exact; the
continuous fiber phase between them is the chart realization.

## Interpolated mode

The control card carries an Interpolated switch, on by default. It
smooths all chart motion between chronons by the sub-chronon
fraction: the drive sweep, the leak drifts, the chart turn, the
hand, the fold clock, the pullback ring, the dial, the sky's drive
and drift, and every phase arrow, which rotates exactly one quarter
per chronon (dlog + 1) and so lands on the next quarter at the
tick. Every angle advances by a constant per-chronon step, so the
interpolation is exact at both endpoints; the smoothing is a chart
convention [approx]. All data stays on the tick: values, labels,
rank tints, and cardinal marks switch only at integer chronons,
riding the interpolated guides. Two exclusions follow from the
data/geometry split: the phase comb's arrows stand in the Carrier
view (the residues stand, so there is nothing to interpolate), and
the Subject view's C232 chart turn steps on the tick (the ring is
232-fold self-similar, so the one-tick turn maps its marks onto
themselves and interpolating it would only wobble). Off restores
exact tick-stepping.

## Layout

The three panels are exactly square, at the same principal-circle
scale (R = 202 of 520), and hold visuals only: all captions sit
under the panels. The control card -- with the unified view toggle
-- sits above the panels so it stays reachable in the portrait mode,
where the panels stack vertically; in landscape they span the full
width.

## The octant bridge and the Borel count

The octant bridge is oriented by the corpus rule: dlog(3w) = 105 = 1
(mod 8), whence i = gen^42 = 5 and c(iu) = h c(u) with the half-lift
carrying one octant step. The Borel count and its cover, kept
strictly apart. The base events:
156 = 72 + 72 + 12 -- the images of tau and of tau + 2 plus the
origin clock's twelve null events, by the explicit bijection
(c, e) -> [x -> g^e x + c]: 144 nonzero-translation events plus
the 12-element origin stabilizer; the visible 48 per shell means
the 24 images at tau with the 24 at tau + 2, base events, never
spin states. The spinor lifts eta and -eta = eta_{tau+12} live
entirely on the cover: the two temporal/spatial covers share
exactly the one sign, gcd(24, 26) = 2, and their central product
(C24 x C26)/<(12, 13)> -- the quotient identifying the two signs,
proven an isomorphism onto C312 by phi(a, b) = 13a + 12b (kernel
exactly {(0,0), (12,13)}, [(1,1)] of order 312) -- is a two-to-one
EVENT-SET cover of the 156, 2 x 156 = 312 (a cyclic group has no
nonabelian AGL(1, 13) quotient; the cover is of sets, not groups).
The observable frame group is
PGL2(F13): its Borel is the affine group AGL(1, 13) of 156 cells,
its nonsplit C14 acts regularly on the fourteen points of P1, 2184 =
156 x 14 stabilizer times transversal; SL2 is the spin double cover
of PSL2 (order 1092, the index-two rotation half of PGL2), where B
and T share the sign -I and |BT| = 1092.
The sky's leak drift is a half-angle on the Carrier's spinor
cover (C464 inside F_233^2, 464 | 54288): the sheet sigC flips at
the Carrier wrap, the drift steps uniformly through it, and the
sky closes with the pair's spinor recurrence, 2 x 696 -- a
proxy-chart datum, tagged in the frame-leak section.

## The frame leak (00:C17, 00:C18)

No Subject is an ideal of the Carrier: a field has no proper
ideals, so the Subject's register never closes inside F_233 and
the Carrier's count passes through it -- every observer inherits
the Carrier clock, every frame is mortal. The panels draw the
consequence. One relative winding, one tick-angle per chronon, and
each view holds its own frame. Subject view: the register and the
sky stand (the sky is register-anchored: both azimuth components
are register data; the drive is hidden by re-registration; the
whole geometry is static and only the values walk), while the
Carrier's chart {1, hbar, -1, h} turns counterclockwise under them
(hbar = 144 the i-oriented quarter and h = 89 the (-i)-oriented,
per the standing audit). Carrier view: the quarters stand (hbar on
top), the drive turns the frame ray and the sky, and the register
drifts clockwise past them, prograde -- the sky at the half rate on
the spinor cover (the sheet sigC carrying continuity through the
Carrier wrap, closure at the spinor recurrence 2 x 696, a
proxy-chart datum). The q/p
dial is one instrument, identical in both views: it reports q's
Carrier address -- a relational datum of the pair -- turning
clockwise one tick-angle per chronon, the address flipping x h per
quarter: q lands on the h cardinal at tau = S = 58. The
frame returns at 232 but the pair phase does not: the joint
closure at 696 = lcm(12, 232), spinor 2 x 696. The closure numbers
are proxy-chart data, tagged as such: a return needs a marked
origin and a memory that spans it, and both belong to the
declaring chart -- the Carrier is a timeless torsor, and the
Subject's faithful budget is its own 12-cycle. The law is
canonical, the event is bookkeeping, and the number reads the
capacity: 696 = S x 12 = kappa x 232, the joint return exactly
S = 58 Subject-cycles out (gcd(kappa, S) = 1), the capacity bound
in the time domain; the spinor double 2S x 12 = 1392 rides the
cover, representation bookkeeping. What the pair itself registers
is the monotone dephasing, one tick-angle per chronon: at
cosmological S the recurrence outruns
every Subject year and C18's winding is
read as the arrow of time.

## The observable meridian M0 (00:Y3, 00:Y5)

The meridian is a light-cone object, exactly as everything the sky
draws: cell a of the additive line is registered at lookback a,
radial step a -- the sky is the past light cone (00:Y3), each
latitude step one chronon deep, the labels retarded (render check
3). The capacity bound resolves exactly kappa radial steps within
the observational horizon (4a < p iff a <= kappa = 3), and these
are the three drawn shells: the observable segment of M0 therefore
threads the existing nodes, cell +-a on shell L_a -- (e, k = a,
s = a - 1) -- machine-pinned at the exact shell radii. The third
node grazes the horizon (sin(6 pi/13) = 0.9927), and the trace
ends at the quarter fold a = 13/4, radius R, marked by an open
tick: beyond the quarter the meridian continues below resolution,
down the scale tower -- past the observational horizon, where no
nodes exist to register it. The unobservable remainder of the
meridian and the absence of shells beyond kappa are one fact: the
capacity bound.

The meridian law is one continuous law per route over a in
[0, 13], and it is the SCALE-TOWER CIRCUIT: colatitude a pi/13,
radius R |sin(2a pi/13)| -- |sin| of the tower angle 2a pi/13, one
full period per cycle, the period points at a = 0, 13/2 (the
1-algebra half, between -1/2 = 6 and +1/2 = 7), and 13. The
radius is the scale coordinate: the photon travels the scales of
the space, never through the Observer's position; its approach to
the origin is the decoherence descent L3 -> L2 -> L1, and
absorption is the completed cascade at registration. The azimuth
follows the transport law with the shell index on the tent
s(a) = a - 1 before the half and 12 - a after, threading the
direct nodes (cells 1, 2, 3 on L1, L2, L3) AND their echoes
(cells -3, -2, -1 at k = 10, 11, 12, azimuth 80 - 5a landing on
the echo nodes exactly; colatitudes of direct and echo sum to pi
-- the distributed sign, machine-pinned residual zero at ten of
the twelve stations). The DRAWN figure is the observable sector
of this circuit: FOUR RAYS per meridian -- ray meaning fiber
geodesic, the full retarded-spiral geometry -- the retarded pair
(per route, the absorption descent; walked outward, the emission)
and the advanced pair, their backwards-in-time shadows (the
advanced cone x g^-1), each from the drawn Observer to the
observational horizon at the quarter fold. The four rays at the
origin realize the four quarter classes: the Q4 channel (00:C20),
drawn. Between the folds the circuit runs below resolution, down
the scale-periodic tower -- unobservable, and not drawn in the
observable sector. The cycle closes because the tower is
periodic: kappa scale steps of four heights each, 4 kappa =
p - 1, one drive revolution. And the drive step factors exactly:
the scale step is the rung ladder x3 = g^4 (order kappa), the
quarter is Ihat = g^{-kappa} = 5 = i (order 4), and heights
4 - 3 = 1 give

    g = g^4 * g^{-3} = 3 * 5 = 2   on F13:

one chronon = one scale step times one quarter turn,
psi_{tau+1} = g psi_tau = i (3 psi_tau) -- the scale descent and
the drive step are one act, seen radially versus temporally (the
CRT factorization C12 = C4 x C3, the channel of 00:C20; the unit
exponents are exact at kappa = 3). Isotropy of emission and
absorption is the family, not the label: the winding family
m = 1..12 under this one law covers the node field completely --
72 of 72 nodes, 24 per shell, multiplicity 1 on odd rows and 3 on
even -- the sheet parity: 36 odd-row nodes once, 36 even-row
nodes thrice, 144 = 36 + 108 slots -- so each drawn
meridian is one label of the covering family, and the mesh
refines down the tower within capacity [approx: density is the
profinite tower statement, capacity-bounded].

The pair geometry is the field pair drawn -- F = E + iB, the two
quadratures of one field (the packaging of [3]). At the
unregistered origin the eight rays launch tangent to the clock
axis, the drive direction: the two quadratures co-propagate, and
no transverse label exists at the origin (ownership; isotropy) --
machine-pinned at under 0.03 degrees. The internal quarter
appears off the origin: the M0/M3 tangents separate through 90
degrees inside the first shell, and at the observational horizon
the pair fuses exactly -- M0's retarded fold point on route e IS
M3's advanced fold point on route -e, and conversely: the quarter
fold enacts the quarter, the duality exchange E <-> B with route
and time both flipped, four horizon points fusing the eight
ray-ends pairwise (residual zero, every clock state). The
winding-m family is ramified at the half cell: all four M3 rays
pass one point exactly at t = 13/10 and 13 - 13/10 -- cell 13/2,
the 1-algebra half, where route and tent degenerate (6.5 =
13 - 6.5); M0's ramification point is the origin itself
(r(13/2) = 0, absorbed in the self-echo). The visible ray
crossings are these exact incidences -- the half-cell
ramification, the axis passages of the winding-5 walk, the
horizon fusions -- plus sub-pixel cell-coincidence passes where
a = +-5t (mod 26); none is accidental. The meridian
parameter passes the Subject's own cell at a = 0, 13/2, 13, and
there the dressing vanishes by ownership: the flow dresses
registered rows -- other cells' registrations -- and no chart
displaces the origin of the observation. Every ray therefore
anchors at the drawn Observer, at every clock state.
The gauge's half-turn needs no unwinding at all: the fiber
rotation by pi is the lift's antipode and the sheet-fair chart is
odd, so the pi-branch acts on the ball as the exact point
reflection, which fixes the Observer; only the balanced quarter
residual sweeps, and near the quarter states its sweep passes the
tangency circle -- the rim kiss, the drawn spinorial quarter
(00:C20). The four rays about the clock axis: the quasar figure.
The deep-lookback rows cross the
atlas sheet under their curl (the lift's q4 through zero); with
the one shared flow map the meridians cross with them, the
crossing visible as the seam bend. Station incidence, causal
ordering, winding, and the registered flow are exact; the
connecting curves are the declared spacetime chart (the guard
projection, the |sin| radial interpolation, the tent law, the
sheet-fair fold, and the ownership ramp are chart conventions,
each declared).

M3, the momentum-quarter dual, joins M0 in the light-cone mode in
momentum red -- and it is the SAME meridian law at winding five.
The walk in the derived quarter direction Ihat = g^{-kappa} = 5
reaches cell +-5t at radial step t; unfolding the colatitude on
the C26 double cover, u = 5t, the node indices follow the fold --
k = u - 13m on even half-winds with the ray's route, k = 26 - u on
odd half-winds with the route flipped, the lift alternating per
half-wind exactly as the helices carry two routes on one loop --
and the azimuth IS the node law PH3 with these continuous
arguments, the curl riding the row k(t) (the sky retards by row;
for M0 the row and the step coincide). The twelve stations per
ray-pair (cells 5, 10, 2 out; 11, 3, 8 home, at the tent shells)
are threaded at residual zero by construction, machine-pinned.
The winding-five curve crosses the poles four times mid-cycle at
exact heights on the clock axis (192.1, 118.7 -- the degenerate
leaf, azimuth-free), and every break of the law hides there or at
the origin bounce. Nodes and guides share ONE
flow law, the retarded common flow: the sky is retarded, so row k
carries the flow of its emission chronon,
phi(k) = -(bC - k) pi/116 = PHI + k CURL. The Carrier view is the
Subject view plus the gauge -- the subject curl k CURL is the
gauge-invariant residue of the retarded flow -- and at the quarter
station bC = S = 58 the origin's twist is exactly -pi/2: the
retardation is a quarter turn, continuously distributed over the
distance from the origin, decaying one tick-angle per row of
lookback. With one law there is nothing to stitch: every station
of both meridians threads exactly in both views at every state
(machine-pinned), the stations are ROW-GRADED -- row k reaches its
congruent parity image at bC = 116 + k and its home at bC = k,
each row at its own retarded epoch (machine-pinned). The guides
anchor at the OBSERVER: the gauge is a property of the registered
rows, so it turns on with registration -- full at k >= 1 (the
stations carry the node law exactly), zero at the origin, the
unregistered here-now, drawn at the centre in every view. The
meridians therefore emanate from the Observer at every state
(machine-pinned to zero), winding the gauge on across the first
row -- the onset coil at the jet base -- while the clock bead
remains the gauge's own display. The meridian flow carries the NORTH FOLD: the
sub-equatorial lift reflects through the S3 equator (q4 -> |q4|,
continuous, stations untouched) -- the sheet sign that aligns the
origin's lift with the bead's pole -- and in consequence the drawn
first step passes the tangency circle: the rim kiss between the
origin and L1, the sheet crossing of the first step, the spinorial
quarter of 00:C20 drawn as geometry. Flowed curves bend where they
cross the atlas seam, as the drive loops do. The 4-sector
structure is M0's: direct arc, horizon fold, beyond-horizon middle
(ultra-faint), far fold, echo arc, closure through the here-now.
M0 and M3 are windings one and Ihat of one law: the meridian
family is the winding ladder, the additive Fourier pair is the
winding pair (1, Ihat), and the E-B reading [tagged] gets its
exact face -- the momentum meridian's delocalization in the
position sky is its five-lobed sweep about the axis, the winding
number drawn. Each lookback step advances the azimuth
by 11 pi/12 + pi/13 + pi/232 -- a near half-turn, sides
alternating, so the spiral is nearly a flat great circle
through the Observer region; its residual per step is
pi/12 - pi/13 - pi/232 = pi/156 - pi/232, the totality half-angle
against the halved Carrier tick: the leak's signature written on
the space trace. The route-minus ray steps by 11 pi/12 - pi/13 +
pi/232 (the route half-angle flips sign): the echo pair's
chirality, visible as the two rays' different pitch. The
supporting geometry stands machine-checked: no plane through the
Observer contains more than two outer nodes, so no single geodesic
threads the full node field -- the full thirteen-cell meridian is
past the horizon, and its complete, simultaneous reconstruction
lives where the register lives, on the shell panel, where M0
crosses every latitude orthogonally at its node. The two panels
draw one structure through two charts: the shell shows space as
the register holds it, the sky shows the kappa steps of it that
light can deliver. The horizon class [1:0] keeps its boost-chart
address, the Cayley half-turn -1 (the Cayley station theorem,
verify-hopf). Lensing and path multiplicity are relational and
arrive with the first Object; emission directions are frame data,
p - 1 azimuths, one drive orbit.

## Provenance

1-phase-6 extends the stable episode 1-phase-5 (kept frozen as the
stable release) with the light-cone reading of the sky made
explicit and the observable meridian: the kappa-step trace of M0
through the L1, L2, L3 nodes to the quarter fold, the coplanarity
obstruction theorem, and the Cayley station theorem for the
horizon class. 1-phase-5 extended 1-phase-4 (frozen) with the relational
dilation: the Subject view draws the retarded boost-curl (00:C18),
the gauge-free observable face of the Dirac flow -- the
gravitational face -- while the harness view keeps the common flow
as the Carrier-referenced chart realization. 1-phase-4 extended 1-phase-3 (frozen)
with the frame dilation in the sheet-fair chart, the leaf-riding
beads, and the clock bead; 1-phase-3 extended 1-phase-2 (frozen)
with the Hopf representation toggle, the frame-leak view
semantics, and the interpolated mode; the shell and phase panels
derive from the standing episode 1-phase-1, the
sky panel from the standing episode 1-space (rev 18). All source
episodes remain frozen; the doctrine sections below the panels
carry their standing constructive descriptions.

## References

[1] Akhtman, Y. Relativistic Algebra over Finite Ring Continuum. Axioms 2025, 14, 636.
[2] Schroedinger and Dirac Dynamics over Finite Substrate, pp202510.1486.
[3] Quantum Observation over Finite Relational Substrate, pp202606.1160.
[4] Gravitation as Phase Synchronisation over a Finite Relational Substrate, pp202606.1018.
[5] Standard-Model Interactions over Finite Relational Substrate, pp202606.1328.
[6] https://github.com/gamayos/frc-numerics/tree/main/docs/1-phase
