# Sandpiles

Implementation of the Abelian sandpile model in Wolfram Language, written for the course *Metodi Computazionali della Fisica* (Università degli Studi di Milano).

The model runs on an arbitrary graph rather than on a fixed lattice. This is the point of the project: it makes it possible to compare how avalanche statistics change with the topology of the underlying network, and to check whether the power-law behaviour usually associated with self-organised criticality survives that change.

## The model

The simulation starts from a graph with no sand and drops grains one at a time on randomly chosen nodes. When a node reaches its threshold it topples, releasing its grains to its neighbours, which may topple in turn and set off a chain reaction. Four observables are recorded for every avalanche:

| observable | definition | column |
|---|---|---|
| size `s` | total number of topplings in the avalanche | 2 |
| area `a` | number of topplings coming from distinct sites | 3 |
| duration `t` | number of propagation steps | 4 |
| radius `r` | maximum graph distance between a toppled site and the origin of the avalanche | 5 |

A graph is represented as an adjacency list, one entry per node, in the form `{neighbours, grains released on toppling, current grains, threshold}`.

## Graph topologies

| function | topology |
|---|---|
| `ret[n, d]` | *d*-dimensional square lattice with `n^d` nodes |
| `tret[n, d, t, est]` | the same lattice with periodic boundary conditions on `t` of its dimensions |
| `err[V, E, est]` | Erdős–Rényi random graph with `V` nodes and `E` edges |
| `alr[n, m, est]` | random tree, growing `n` times by up to `m` children |
| `baa[in, t, m, es]` | Barabási–Albert preferential-attachment graph grown from a seed graph `in` |

The `est` / `es` argument sets how many external points the graph is given, that is, how many nodes can shed sand out of the system.

## Two algorithms for the radius

The radius is the one observable that is not obtained for free while the avalanche propagates, so it is computed twice, by different routes, and the two implementations are compared:

- `raggio` grows concentric shells around the seed node with `circ`, and stops at the last radius whose shell is still entirely contained in the avalanche.
- `raggio1` computes the maximum distance from the seed over all toppled sites, using `disz` on top of `riga`, which builds the distances from one node to every node of higher index.

Both `circ`, `riga` and `disz` memoise their results, and `disz` stores each distance symmetrically, so the cost of the distance structure is paid once per graph rather than once per avalanche.

## What the analysis found

`plow` bins an observable into `{value, count}` pairs for inspection on log-log axes.

- The power-law behaviour does **not** hold on every topology. On the random tree in particular the distribution does not follow a power law, so the result usually quoted for the lattice cannot be carried over to an arbitrary graph.
- The simulation is faster on the Erdős–Rényi graph than on the lattice even when the two have the same number of nodes, edges and external points. The explanation is that fewer grains topple over the course of the run.
- That suggests the execution time is proportional to the number of grains toppled. The hypothesis is tested by comparing the ratios of the slopes of the linear fits: using the second radius method the values are `2.35 × 10⁻⁵` for the random graph and `2.22 × 10⁻⁵` for the lattice.

## Files

| file | content |
|---|---|
| `bella.m` | the package: simulation, graph constructors, radius algorithms, analysis helpers |
| `bella.nb` | the notebook used to run the simulations and produce the figures |
| `relazione.pdf` | the full report, with the figures, the statistical analysis and the efficiency study (in Italian) |

## Usage

```wolfram
Get["bella.m"]

g    = ret[20, 2];            (* 400-node square lattice *)
data = sim[g, 100000];        (* drop 100000 grains *)

sizes = estr[data, 100000, 2];   (* size of every avalanche *)
hist  = plow[data, 100000, 2];   (* {value, count} pairs, ready for a log-log plot *)
degr[g]                          (* degree sequence of the graph *)
```

`estr` and `plow` take the output of `sim`; their last argument selects the observable by the column numbers given in the table above.

## A note on naming

Identifiers and the report are in Italian, since this was coursework: `sim` runs the simulation, `metti` drops a grain, `val` follows an avalanche, `distribuisci` performs a toppling, `circ` returns a shell, `raggio` the radius.
