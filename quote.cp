new [a:forall bool.forall int.forall int.exists int.1]
    (a*(b).[if b
            then [a*(x).a*(y).a*[x + y].a[].0 |- a:forall int.forall int.exists int.1]
            else [a*(x).a*(y).a*[x + (-1 * y)].a[].0 |- a:forall int.forall int.exists int.1]] |
     a*[false].a*[55].a*[13].a*(x).b*[x].a().b[].0)
 |- b:exists int.1.

new [a:forall int. +{ok:1,bad:1}]
    (a*(i).[if isZero i then [a/ok.a[].0 |- a: +{ok:1,bad:1}] else [a/bad.a[].0 |- a: +{ok:1,bad:1}]] |
     a*[0].a<->b) |- b:+{ok:1,bad:1}.


new [a:forall int.exists int.1]
    (a*(i).a*[(fix (\f:int -> int. \n:int. if isZero n then 1 else n * f (n + (-1)))) i].a[].0 |
     a*[5].a<->b)
  |- b:exists int.1.