type Church = forall X.?(X * ~X) || (~X || X).
def Two(x) = x(X).x(s).x(z).?s[f].f[a].(a<->z | ?s[g].g[b].(f <-> b | g <-> x)).
def One(x) = x(X).x(s).x(z).?s[f].f[a].(a<->z | f<->x).
def Zero(x) = x(X).x(s).x(z).z<->x.
def Ping(x,y,w) = x[1].x[s].(!s(f).f(a).a().?y[u].u().f[].0 | x[z].(z[].0 | x().w[].0)).
new [x:Church] (Zero(x) | Ping(x,y,w)) |- y:?bot,w:1.
new [x:Church] (One(x) | Ping(x,y,w)) |- y:?bot,w:1.
new [x:Church] (Two(x) | Ping(x,y,w)) |- y:?bot,w:1.
type Top = &{}.
new [y1 : !Top * !Top] (foo <-> y1 |  y1(x2).!z0(y3).case y3(){}) |- foo : ~(!Top * !Top),z0:!Top.
