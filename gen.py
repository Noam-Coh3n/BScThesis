import sys

try:
    opt = sys.argv[1]
except IndexError:
    opt = "disj"

try:
    N = int(sys.argv[2])
except IndexError:
    N = 51

if __name__ == "__main__":
    match opt:
        case "disj":
            formulas = [" ∨∨ ".join(f"prop {j}" for j in range(1, i+1))
                        for i in range(1, N+1)]
        case "star":
            formulas = ["dim (" + "star ("*i + "atom 0" + ")"*i + ") (prop 1)"
                        for i in range(N)]
        case "star_test_rec":
            formulas = ["prop 1"]
            for i in range(N):
                formulas.append(f"dim (star (test ({formulas[i]}))) (prop {i+2})")
        case "star_union":
            formulas = ["dim ("
                        + " ∪∪ ".join(("star ("*j + f"atom {j}" + ")"*j) for j in range(i))
                        + ") (prop 1)"
            for i in range(1, N+1)]
        case _:
            raise ValueError(f"Unknown option {opt}")

    with open("CyclicFormulas/Input.lean", 'w') as f:
        f.write("import CyclicFormulas.Formula\n\nopen Formula Program\n\n")
        f.write("def list_formulas : List Formula := [" + ", ".join(formulas) + "]")
