cut [a:forall bool.forall int.forall int.exists int.1]
    (a*(b).[if b
            then [a*(x).a*(y).a*[x + y].a[].0 |- a:forall int.forall int.exists int.1]
            else [a*(x).a*(y).a*[x + (-1 * y)].a[].0 |- a:forall int.forall int.exists int.1]] |
     a*[false].a*[55].a*[13].a*(x).b*[x].a().b[].0)
 |- b:exists int.1.
