import matplotlib.pyplot as plt
import numpy as np
from gen import opt, N


if __name__ == "__main__":
    x = list(range(N))
    y = [int(x) for x in input().split()]

    if opt == "star_union":
        fig, ax = plt.subplots()
        ax.plot(x, y, 'b', label=r"$\mathbb{G}_{\psi_i}$")
        ax.set(xlabel="$i$", ylabel="number of states")
        ax.grid(which='both')
        ax.minorticks_on()
        fig.legend(fontsize=18)

        figl, axl = plt.subplots()
        axl.loglog(x, y, 'b', label=r"$\mathbb{G}_{\psi_i}$")
        # axl.loglog(x, [a*a for a in x], 'r-')
        axl.set(xlabel="$i$", ylabel="number of states")
        axl.grid('both')
        mm = axl.axline((x[-2], y[-2]), (x[-1], y[-1]), c='g', linestyle='--')
        axl.minorticks_on()
        figl.legend(fontsize=18)
        figl.savefig(f"{opt}_{N}_loglog.png")
    elif opt == "disj":
        fig, ax = plt.subplots()
        ax.plot(x, y, label=r"$\mathbb{G}_{\varphi_i}$")
        ax.set(xlabel="$i$", ylabel="number of states",
               title="Disjunction of proposition letters")
        ax.grid(which='both')
        ax.legend(fontsize=18)
        ax.minorticks_on()

    fig.savefig(f"{opt}_{N}.png")