## Attribute closure algorithm
function attribute_closure(Y::Set{String}, S::Set)
    """Given a set of attributes `Y` and some set of functional dependencies
    `S`, returns the closure of attributes `Y`.
    """
    Y_plus = deepcopy(Y)
    did_change = true
    while did_change
        did_change = false
        for pair_ in S
            lhs = pair_[1]
            rhs = pair_[2]
            if issubset(lhs, Y_plus)
                if !issubset(rhs,Y_plus)
                    did_change = true
                    union!(Y_plus, rhs)
                end
            end
        end
    end

    return Y_plus
end

## Closure test: Function to see if a given functional dependence follows
 # from a set of attributes `S`

function fd_follows(S::Set, FD::Pair{Set{String},Set{String}})
    """Given a potential functional dependence FD, we return
    `true` if it is implied by the functional dependencies in `S`
    and `false` if not.
    """
    LHS = FD[1]
    RHS = FD[2]

    Y_plus = attribute_closure(LHS, S)
    return issubset(RHS, Y_plus)
end

## Projection algorithm: Given some set of functional dependencies  and a
 # subset of attributes `L`, we return all the FD's that follow from the
 # original set that ONLY concern attributes in `L`
function project(S::Set, L::Set{String})
    """Project the functional dependencies in `S` onto the attributes
    in `L`.
    """
    T = Set()

    L_list = [el for el in L]

    L_powerset = collect(powerset(L_list))
    for X in L_powerset
        X_set = Set(X)
        X_set_closure = attribute_closure(X_set, S)
        println("X_set is ", X_set, " with closure ", X_set_closure)
        for A in X_set_closure # a is a string representing 1 attribute
            if A in L && !(A in X)
                println("\tAdding attribute ", A, " because it is in `L` and NOT in `X`")
                push!(T, Set(X)=>Set([A]))
            end
        end
        # @info X_set X_set_closure
    end

    return T
end

## Minimal basis: A minimal basis will have 3 important properties,
 # 1. No redundant functional dependencies.
 # 2. No functional dependencies with unnecessary attributeson the LHS.
 # 3. All RHS are single attributes.

function minimal_basis(S::Set)
    """Takes `S`, a set of pairs of sets, and returns the minimal basis.
    S has the form Set([
            Set(["A", "B"]) => Set(["C"]),
            ...
        ])
    """
    S_min::Set{Pair{ Set{String}, Set{String} }} = Set()
    # 1: Split the right hand side of each pair in S
    for pair_ in S
        lhs = pair_[1]
        rhs = pair_[2]

        for attribute in rhs
            # println(typeof(attribute))
            push!(S_min, lhs => Set([attribute]))
        end
    end

    println("\nAfter splitting all attributes, S_min is: ")
    for pair in S_min
        println("\t",pair)
    end

    println("\nBeginning step 2: removing LHS attributes where possible.")
    # 2: Removing attributes where possible.
    did_remove = true # flag: whether we were able to remove anything.
    while did_remove
        did_remove = false
        # Looping through S_min's attributes, looking for |LHS| ≥ 2
        for pair_ in S_min
            lhs = pair_[1]
            rhs = pair_[2]

            if(length(lhs) >= 2)
                for remove_this in lhs
                    new_lhs = setdiff(lhs, Set([remove_this]) )
                    new_pair = new_lhs=>rhs
                    is_known = new_pair in S_min

                    if (!is_known && fd_follows(S_min, new_lhs=>rhs)) # it does follow...
                        println("\tAble to remove attribute ", remove_this, " from ", lhs=>rhs)
                        println("\t\tAdding replacement ", new_lhs=>rhs)
                        push!(S_min, new_lhs=>rhs)
                        S_min = setdiff(S_min, Set([lhs=>rhs]))
                        # pop!(S_min, lhs=>rhs)
                        did_remove = true
                        break
                    elseif is_known && fd_follows(S_min, new_lhs=>rhs)
                        println("\tStronger version of ", lhs=>rhs, " is already known: ", new_lhs=>rhs)
                        println("\t\tDeleting ", lhs=>rhs)
                        pop!(S_min, lhs=>rhs)
                        did_remove = true
                        break
                    end
                end
            end
            if did_remove
                break
            end
        end
    end

    println("\nAfter removing redundant LHS terms, S_min is: ")
    for pair in S_min
        println("\t",pair)
    end

    println("\nBeginning step 3: removing redundant FD's...")
    # 3: Removing redundant FD's
    did_remove = true
    while did_remove
        did_remove = false
        for pair_ in S_min
            S_min_potential = setdiff(S_min, Set([pair_]))
            if fd_follows(S_min_potential, pair_)
                println("\tAble to remove ",pair_," without changing FD's!")
                pop!(S_min, pair_)
                did_remove = true
                break
            end
        end
    end
    return S_min
end
