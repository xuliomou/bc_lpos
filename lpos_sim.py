#!/usr/bin/env python3
"""
Simulador de Leased Proof of Stake (LPoS) estilo Nxt/Waves.

Uso:
    python lpos_sim.py 1          # Escenario 1: forja proporcional (Nxt vs Fair PoS)
    python lpos_sim.py 2          # Escenario 2: centralización de pools
    python lpos_sim.py todo       # los dos seguidos (también sin argumentos)
    python lpos_sim.py 2 --guardar   # además guarda la gráfica en PNG
    python lpos_sim.py 1 --semilla 7 # repite el experimento con otra semilla

Sin --semilla se usa siempre la semilla por defecto (42).
La semilla fija el bloque génesis (y, en el escenario 2, las decisiones de los
usuarios). Con la misma semilla los resultados son reproducibles; cambiándola
se comprueba que las conclusiones no dependen de la suerte.

Requisitos: Python 3.8+ y matplotlib (pip install matplotlib)
"""
import hashlib
import math
import argparse
import random
from collections import defaultdict

import matplotlib.pyplot as plt

# ---------------------------------------------------------------------------
# Parámetros del protocolo (los de Waves)
# ---------------------------------------------------------------------------
VENTANA_GENERATING = 1000   # generating = mínimo del effective en los últimos 1000 bloques
MIN_GENERATING = 1000       # hacen falta 1000 monedas de generating para forjar
SEMILLA = 42                # se puede cambiar con --semilla N
TIEMPO_OBJETIVO = 60.0      # segundos entre bloques que se quieren conseguir
X_MAX = 2**64               # el hit son 8 bytes de un hash


def h(*partes: bytes) -> bytes:
    return hashlib.sha256(b"".join(partes)).digest()


# ---------------------------------------------------------------------------
# Libro de cuentas: saldos, leases y historial del saldo effective
# ---------------------------------------------------------------------------
class Ledger:
    def __init__(self):
        self.regular = {}                     # R: saldo propio
        self.leases = {}                      # id -> (arrendador, nodo, cantidad)
        self.lo = defaultdict(int)            # Lo: arrendado a otros
        self.li = defaultdict(int)            # Li: recibido en lease
        self.historial = defaultdict(list)    # cuenta -> [(altura, effective)]
        self.altura = 0
        self._siguiente_id = 0

    def crear_cuenta(self, nombre, saldo):
        self.regular[nombre] = saldo
        self._registrar(nombre)

    def effective(self, c):
        return self.regular[c] - self.lo[c] + self.li[c]

    def available(self, c):
        return self.regular[c] - self.lo[c]

    def _registrar(self, c):
        self.historial[c].append((self.altura, self.effective(c)))

    def lease(self, arrendador, nodo, cantidad):
        """LeaseTransaction: cede peso de stake, NO mueve las monedas."""
        assert cantidad <= self.available(arrendador), "saldo disponible insuficiente"
        lid = self._siguiente_id
        self._siguiente_id += 1
        self.leases[lid] = (arrendador, nodo, cantidad)
        self.lo[arrendador] += cantidad
        self.li[nodo] += cantidad
        self._registrar(arrendador)
        self._registrar(nodo)
        return lid

    def cancelar_lease(self, lid):
        """LeaseCancelTransaction: devuelve el peso al propietario."""
        arrendador, nodo, cantidad = self.leases.pop(lid)
        self.lo[arrendador] -= cantidad
        self.li[nodo] -= cantidad
        self._registrar(arrendador)
        self._registrar(nodo)

    def generating(self, c):
        """Mínimo del effective en los últimos VENTANA_GENERATING bloques.
        Una BAJADA cuenta al instante; una SUBIDA tarda 1000 bloques en contar."""
        desde = self.altura - VENTANA_GENERATING
        minimo = None
        for altura, valor in reversed(self.historial[c]):
            minimo = valor if minimo is None else min(minimo, valor)
            if altura <= desde:      # este valor ya estaba vigente al inicio de la ventana
                break
        return minimo


# ---------------------------------------------------------------------------
# Forja: quién genera el siguiente bloque
# ---------------------------------------------------------------------------
def hit_de(gen_sig: bytes, clave_publica: bytes) -> int:
    """hit = primeros 8 bytes de H(genSig || pk)  (diapositiva 2.1)"""
    return int.from_bytes(h(gen_sig, clave_publica)[:8], "big")


def retardo(hit: int, generating: int, base_target: float, modo: str) -> float:
    """Segundos que el nodo tiene que esperar para poder forjar.

    Modo 'nxt': el nodo puede forjar cuando  hit < target,
        con target = baseTarget * generating * t   (crece con el tiempo t).
        Despejando, el instante en que se cumple es  t = hit / (baseTarget * generating).
        Esperar ese tiempo y comprobar hit < target cada segundo es lo MISMO.

    Modo 'fair' (Fair PoS de Waves, simplificado): mete un logaritmo,
        t = -ln(hit / X_MAX) / (baseTarget * generating).
        Así la probabilidad de ganar es exactamente proporcional al stake.
    """
    u = (hit + 1) / X_MAX                       # hit normalizado en (0, 1]
    if modo == "nxt":
        return u / (base_target * generating)
    return -math.log(u) / (base_target * generating)


class Red:
    def __init__(self, ledger: Ledger, nodos, modo="fair"):
        self.L = ledger
        self.nodos = list(nodos)
        self.pk = {n: h(n.encode()) for n in self.nodos}   # "clave pública" ficticia
        self.modo = modo
        self.gen_sig = h(b"bloque genesis", str(SEMILLA).encode())
        total = sum(self.L.effective(n) for n in self.nodos)
        self.base_target = 1.0 / (TIEMPO_OBJETIVO * total)
        self.ultimos_tiempos = []
        self.cadena = []                                     # ganador de cada bloque

    def forjar_bloque(self):
        L = self.L
        mejor, mejor_t = None, float("inf")
        for n in self.nodos:
            g = L.generating(n)
            if g < MIN_GENERATING:
                continue                                     # no llega al mínimo
            t = retardo(hit_de(self.gen_sig, self.pk[n]), g, self.base_target, self.modo)
            if t < mejor_t:
                mejor, mejor_t = n, t
        if mejor is None:
            raise RuntimeError("ningún nodo tiene generating suficiente")

        # El ganador publica el bloque: nueva firma de generación encadenada
        self.gen_sig = h(self.gen_sig, self.pk[mejor])
        self.cadena.append(mejor)
        L.altura += 1

        # Ajuste de baseTarget (regla de Waves) para mantener ~60 s por bloque
        self.ultimos_tiempos = (self.ultimos_tiempos + [mejor_t])[-3:]
        media = sum(self.ultimos_tiempos) / len(self.ultimos_tiempos)
        if media > 90:
            self.base_target *= 1.01
        elif media < 30:
            self.base_target *= 0.99
        return mejor, mejor_t

    def forjar(self, n_bloques):
        tiempos = [self.forjar_bloque()[1] for _ in range(n_bloques)]
        return sum(tiempos) / len(tiempos)


def coeficiente_nakamoto(cuotas):
    """Mínimo número de nodos que juntos superan el 50 %."""
    acumulado = 0
    for i, c in enumerate(sorted(cuotas, reverse=True), 1):
        acumulado += c
        if acumulado > 0.5:
            return i
    return len(cuotas)


# ---------------------------------------------------------------------------
# Escenario 1: ¿los bloques son proporcionales al stake?
# ---------------------------------------------------------------------------
def red_basica(modo):
    """5 nodos con 1000 propios + leases de usuarios hasta su cuota de stake."""
    L = Ledger()
    reparto = {"Nodo A": 40, "Nodo B": 25, "Nodo C": 15, "Nodo D": 12, "Nodo E": 8}
    for nodo, pct in reparto.items():
        L.crear_cuenta(nodo, 1000)
        usuario = f"usuarios de {nodo}"
        cantidad = pct * 10_000 - 1000
        L.crear_cuenta(usuario, cantidad)
        L.lease(usuario, nodo, cantidad)
    L.altura = VENTANA_GENERATING      # arrancamos con el stake ya maduro
    return L, list(reparto), reparto


def escenario_1(guardar=False):
    print("\n=== ESCENARIO 1: forja proporcional al stake ===")
    resultados = {}
    for modo in ("nxt", "fair"):
        L, nodos, reparto = red_basica(modo)
        red = Red(L, nodos, modo)
        media = red.forjar(5000)
        cuenta = {n: red.cadena.count(n) / len(red.cadena) * 100 for n in nodos}
        resultados[modo] = cuenta
        print(f"\nModo {modo.upper()}  (tiempo medio de bloque: {media:.0f} s)")
        for n in nodos:
            print(f"  {n}: stake {reparto[n]:>3} %  ->  bloques {cuenta[n]:5.1f} %")

    x = range(len(nodos))
    fig, ax = plt.subplots(figsize=(9, 5))
    ax.bar([i - 0.27 for i in x], [reparto[n] for n in nodos], 0.27, label="% del stake")
    ax.bar(list(x), [resultados["nxt"][n] for n in nodos], 0.27, label="% bloques (fórmula Nxt)")
    ax.bar([i + 0.27 for i in x], [resultados["fair"][n] for n in nodos], 0.27, label="% bloques (Fair PoS)")
    ax.set_xticks(list(x), nodos)
    ax.set_ylabel("%")
    ax.set_title("Escenario 1 · ¿Gana bloques cada nodo según su stake? (5000 bloques)")
    ax.legend()
    _mostrar(fig, "escenario1.png", guardar)


# ---------------------------------------------------------------------------
# Escenario 2: los arrendadores se van al pool más grande
# ---------------------------------------------------------------------------
def escenario_2(guardar=False, epocas=10, bloques_por_epoca=1000, prob_cambio=0.15):
    print("\n=== ESCENARIO 2: centralización de pools ===")
    rnd = random.Random(SEMILLA)
    L = Ledger()
    nodos = [f"Pool {i}" for i in range(1, 9)]
    leases_de = {}                                   # usuario -> (id lease, nodo)
    for i, nodo in enumerate(nodos):
        L.crear_cuenta(nodo, 1000)
        for j in range(25):
            u = f"usuario {i}-{j}"
            L.crear_cuenta(u, rnd.randint(500, 5000))
            leases_de[u] = (L.lease(u, nodo, L.available(u)), nodo)
    L.altura = VENTANA_GENERATING
    red = Red(L, nodos, "fair")

    historia_cuotas, historia_nakamoto = [], []
    for e in range(epocas):
        total = sum(L.effective(n) for n in nodos)
        cuotas = {n: L.effective(n) / total for n in nodos}
        historia_cuotas.append(cuotas)
        historia_nakamoto.append(coeficiente_nakamoto(cuotas.values()))
        print(f"  Época {e:2}: coeficiente de Nakamoto = {historia_nakamoto[-1]}   "
              f"pool mayor = {max(cuotas.values()) * 100:4.1f} %")

        inicio = len(red.cadena)
        red.forjar(bloques_por_epoca)
        bloques = defaultdict(int)
        for n in red.cadena[inicio:]:
            bloques[n] += 1
        favorito = max(nodos, key=lambda n: bloques[n])   # el que más ha pagado

        # Cada usuario, con cierta probabilidad, se cambia al pool favorito
        for u, (lid, nodo) in list(leases_de.items()):
            if nodo != favorito and rnd.random() < prob_cambio:
                L.cancelar_lease(lid)
                leases_de[u] = (L.lease(u, favorito, L.available(u)), favorito)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    for n in nodos:
        ax1.plot([c[n] * 100 for c in historia_cuotas], marker="o", label=n)
    ax1.axhline(50, ls="--", c="red", lw=1)
    ax1.set_xlabel("época (1000 bloques)")
    ax1.set_ylabel("% del stake efectivo")
    ax1.set_title("Cuota de cada pool")
    ax1.legend(fontsize=8)
    ax2.plot(historia_nakamoto, marker="o", c="black")
    ax2.set_ylim(0, max(historia_nakamoto) + 1)
    ax2.set_xlabel("época (1000 bloques)")
    ax2.set_title("Coeficiente de Nakamoto")
    fig.suptitle("Escenario 2 · Los arrendadores se van al pool que más paga")
    _mostrar(fig, "escenario2.png", guardar)


def _mostrar(fig, nombre, guardar):
    fig.tight_layout()
    if guardar:
        fig.savefig(nombre, dpi=150)
        print(f"  (gráfica guardada en {nombre})")
    plt.show()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Simulador de Leased Proof of Stake")
    parser.add_argument("escenario", nargs="?", default="todo", choices=["1", "2", "todo"],
                        help="escenario a ejecutar (por defecto: todo)")
    parser.add_argument("--semilla", type=int, default=SEMILLA,
                        help=f"semilla del experimento (por defecto: {SEMILLA})")
    parser.add_argument("--guardar", action="store_true",
                        help="guarda las gráficas en PNG")
    args = parser.parse_args()

    SEMILLA = args.semilla
    print(f"(semilla = {SEMILLA})")
    if args.escenario in ("1", "todo"):
        escenario_1(args.guardar)
    if args.escenario in ("2", "todo"):
        escenario_2(args.guardar)
