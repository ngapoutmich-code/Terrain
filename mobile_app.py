# -*- coding: utf-8 -*-
"""
mobile_app.py — Consultation MOBILE (lecture seule) des données Mich4Track.

  * Connexion par compte personnel (mots de passe hachés bcrypt, table mobile_utilisateurs).
  * 3 vues : Aperçu (chiffres clés) · Rapports (par essence, par titre, essence × titre) ·
    Rechercher (DF10 / code barre / N° LV, ou SÉQUENCE).
  * Lit la copie en ligne (Neon) avec le rôle en LECTURE SEULE : aucune écriture possible.
  * Mêmes définitions que Billon_app :
        perte  = volume grume mère − somme des billes filles (grumes billonnées)
        évacué = filles en Parc de rupture / Parc usine / En négoce, hors Abandon
        usiné  = billons en situation « Parc usine » (hors Abandon), par site pour la ventilation
        séquence : « 457 » trouve les séquences qui SE TERMINENT par 457 (457, 1457, 20457…)

Configuration : .streamlit/secrets.toml (jamais dans le dépôt) — voir secrets.toml.example.
Lancement local :  streamlit run mobile_app.py
"""
from __future__ import annotations

import base64
import hashlib
import html
import io
import logging
import json
import math
import os
import random
import re
import secrets
import time
import zlib
from datetime import date, datetime, timedelta, timezone

import bcrypt
import pandas as pd
import psycopg2
import psycopg2.extras
import psycopg2.pool
import streamlit as st

import carte_abattage
import chargement
import chargement_foret
import rapport_chantier
import hors_ligne
import terrain
import partage

journal = logging.getLogger("mich4track")

st.set_page_config(page_title="Mich4Track", page_icon="🌲", layout="wide",
                   initial_sidebar_state="collapsed")

SITUATIONS_EVACUEES = ["PARC DE RUPTURE", "PARC USINE", "EN NÉGOCE", "EN NEGOCE"]
TTL_DONNEES = 300          # secondes : les requêtes sont gardées 5 min (bouton « Actualiser »)
MAX_ECHECS = 5             # échecs de connexion tolérés ...
FENETRE_ECHECS = 15 * 60   # ... sur cette durée (secondes) par identifiant
MAX_GRUMES_RECHERCHE = 20   # fiches affichées d'un coup ; « Afficher plus » en ajoute autant
MAX_BILLES_SEQUENCE = 300  # billes retenues par séquence saisie (la correspondance exacte passe d'abord)
MAX_CARTES = 500           # cartes affichées dans un rapport (pratiquement toutes)

# Une couleur stable par essence (le tri ne change pas les couleurs)
COULEURS_ESSENCES = {
    "SAPELLI": "#2D6A4F", "AYOUS": "#D4B13A", "ASSAMELA": "#B5503C", "TALI": "#C27C2F",
    "IROKO": "#8A5A44", "FRAKE": "#7FAF8A", "OKAN": "#3F7F9C", "SIPO": "#7A6AA8",
    "ACAJOU": "#9C3D3D", "DABEMA": "#5E8C3A", "ABALE": "#A9A58E", "PADOUK": "#D9663F",
    "TIAMA": "#4C9F9B", "BETE": "#8E5B8F",
}
PALETTE_DEFAUT = ["#3F7F9C", "#7A6AA8", "#B94A44", "#5E8C3A", "#A0763C", "#4C9F70", "#9C4A6B", "#6C8EAD"]

# Étapes de la filière (mêmes couleurs partout : forêt → bois)
ETAPES = [("Abattu", "abattu", "#2D6A4F"), ("Exploité", "billonne", "#52B788"),
          ("Évacué", "evacue", "#C9A27A"), ("Usiné", "usine", "#7A4E2D")]


# ---------------------------------------------------------------------------
# Décor vectoriel — cernes d'arbre en filigrane, feuillages en traits fins, rondins gravés.
# Dessiné ici (aucune image externe). Sert de FOND à l'écran de connexion et, très discret, à l'application.
# ---------------------------------------------------------------------------
def _b64(svg: str) -> str:
    return "data:image/svg+xml;base64," + base64.b64encode(svg.encode("utf-8")).decode("ascii")


def _phases(rnd) -> list:
    """Quelques ondulations lentes : tous les cernes d'un même arbre les partagent (croissance réaliste)."""
    return [(rnd.uniform(.5, 1.0), rnd.uniform(0, 6.283), rnd.randint(2, 5)) for _ in range(3)]


def _poly(cx, cy, r, phases, amp, pts=84) -> str:
    """Contour organique fermé : un cercle légèrement déformé."""
    d = []
    for i in range(pts):
        a = 2 * math.pi * i / pts
        k = 1 + amp * sum(w * math.sin(f * a + ph) for w, ph, f in phases)
        d.append(f"{cx + r * k * math.cos(a):.1f} {cy + r * k * math.sin(a):.1f}")
    return "M" + " L".join(d) + " Z"


def _cernes(cx, cy, rmax, n, rnd, couleur, op=(.05, .14), larg=(.7, 1.8), amp=.018, rmin=.05, ph=None) -> str:
    """Cernes de croissance concentriques, espacement et épaisseur irréguliers."""
    ph = ph or _phases(rnd)
    out = []
    for i in range(n):
        t = min(1.0, (i + 1 + rnd.uniform(-.28, .28)) / n)
        r = rmax * (rmin + (1 - rmin) * t)
        out.append(f'<path d="{_poly(cx, cy, r, ph, amp * (.3 + .7 * t))}" fill="none" stroke="{couleur}" '
                   f'stroke-opacity="{rnd.uniform(*op):.3f}" stroke-width="{rnd.uniform(*larg):.2f}" '
                   f'stroke-linejoin="round"/>')
    return "".join(out)


_LANCE = "M0 0 C 34 -28 44 -96 0 -152 C -44 -96 -34 -28 0 0 Z"


def _nervures(nerv: int = 5) -> str:
    return "".join(
        f"M0 {-k * 24} Q {10 - k} {-k * 24 - 4} {21 - k * 2.4:.1f} {-k * 24 - 15} "
        f"M0 {-k * 24} Q {-10 + k} {-k * 24 - 4} {-(21 - k * 2.4):.1f} {-k * 24 - 15} " for k in range(1, nerv + 1))


def _feuille_trait(x, y, rot, s, col, op, larg=1.5, plein=None) -> str:
    """Feuille dessinée au trait fin (contour + nervures), éventuellement teintée d'un voile menthe."""
    fond = f'fill="url(#{plein})"' if plein else 'fill="none"'
    return (f'<g transform="translate({x:.1f} {y:.1f}) rotate({rot:.1f}) scale({s:.3f})" opacity="{op}">'
            f'<path d="{_LANCE}" {fond} stroke="{col}" stroke-width="{larg / s:.2f}" stroke-linejoin="round"/>'
            f'<path d="M0 8 L0 -140 {_nervures()}" stroke="{col}" stroke-width="{larg * .75 / s:.2f}" fill="none" '
            f'stroke-linecap="round" stroke-opacity=".85"/></g>')


def _feuille_pleine(x, y, rot, s, op=1.0, flou=None, nerv=True) -> str:
    """Grande feuille en aplat dégradé (profondeur de champ quand elle est floutée)."""
    f = f' filter="url(#{flou})"' if flou else ""
    v = (f'<path d="M0 8 L0 -140 {_nervures()}" stroke="#fff" stroke-opacity=".30" stroke-width="1.4" fill="none" '
         f'stroke-linecap="round"/>') if nerv else ""
    return (f'<g transform="translate({x:.1f} {y:.1f}) rotate({rot:.1f}) scale({s:.3f})" opacity="{op}"{f}>'
            f'<path d="{_LANCE}" fill="url(#feuillage)"/>{v}</g>')


def _rameau(p0, p1, p2, p3, n, taille, rnd, col, op, larg=1.4, plein=None, ecart=(44, 62)) -> str:
    """Rameau courbe (Bézier) portant des feuilles au trait, alternées, de plus en plus petites vers la pointe."""
    def pt(t):
        u = 1 - t
        return (u ** 3 * p0[0] + 3 * u * u * t * p1[0] + 3 * u * t * t * p2[0] + t ** 3 * p3[0],
                u ** 3 * p0[1] + 3 * u * u * t * p1[1] + 3 * u * t * t * p2[1] + t ** 3 * p3[1])

    def ang(t):
        u = 1 - t
        dx = 3 * u * u * (p1[0] - p0[0]) + 6 * u * t * (p2[0] - p1[0]) + 3 * t * t * (p3[0] - p2[0])
        dy = 3 * u * u * (p1[1] - p0[1]) + 6 * u * t * (p2[1] - p1[1]) + 3 * t * t * (p3[1] - p2[1])
        return math.degrees(math.atan2(dy, dx)) + 90
    tige = (f'<path d="M{p0[0]:.0f} {p0[1]:.0f} C {p1[0]:.0f} {p1[1]:.0f}, {p2[0]:.0f} {p2[1]:.0f}, '
            f'{p3[0]:.0f} {p3[1]:.0f}" fill="none" stroke="{col}" stroke-opacity="{op}" stroke-width="{larg * 1.3:.1f}" '
            f'stroke-linecap="round"/>')
    feuilles = []
    for i in range(n):
        t = .1 + .8 * i / max(1, n - 1)
        x, y = pt(t)
        cote = 1 if i % 2 == 0 else -1
        feuilles.append(_feuille_trait(x, y, ang(t) + cote * rnd.uniform(*ecart), taille * (1.0 - .5 * t), col, op,
                                       larg, plein if (plein and i % 3 == 1) else None))
    x, y = pt(1)
    feuilles.append(_feuille_trait(x, y, ang(1) + rnd.uniform(-6, 6), taille * .5, col, op, larg))
    return tige + "".join(feuilles)


def _defs() -> str:
    return ('<linearGradient id="menthe" x1="0" y1="1" x2="0" y2="0"><stop offset="0" stop-color="#52B788" stop-opacity=".08"/>'
            '<stop offset="1" stop-color="#D8F3DC" stop-opacity=".40"/></linearGradient>'
            '<linearGradient id="feuillage" x1="0" y1="1" x2=".35" y2="0"><stop offset="0" stop-color="#1F6B49"/>'
            '<stop offset="1" stop-color="#7ACF9E"/></linearGradient>'
            '<filter id="flou" x="-40%" y="-40%" width="180%" height="180%"><feGaussianBlur stdDeviation="10"/></filter>'
            '<filter id="flou2" x="-40%" y="-40%" width="180%" height="180%"><feGaussianBlur stdDeviation="3"/></filter>')


# --- Feuillage du haut de l'écran de connexion ----------------------------------
def art_feuilles() -> str:
    """Feuillage léger (viewBox 800 × 460) : deux rameaux au trait fin, quelques lucioles."""
    rnd = random.Random(21)
    lucioles = "".join(
        f'<circle cx="{rnd.uniform(120, 680):.0f}" cy="{rnd.uniform(70, 330):.0f}" r="{rnd.uniform(2.5, 6):.1f}" '
        f'fill="#E3F8E8" opacity="{rnd.uniform(.04, .10):.2f}" filter="url(#flou2)"/>' for _ in range(10))
    menthe = "#C4EBD0"
    r1 = _rameau((-30, -10), (150, 20), (250, 110), (290, 215), 7, .78, rnd, menthe, .50, 1.2, "menthe")
    r2 = _rameau((830, -10), (650, 20), (550, 100), (510, 200), 7, .76, rnd, menthe, .50, 1.2, "menthe")
    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 800 460"><defs>{_defs()}</defs>'
           f'{lucioles}{r1}{r2}</svg>')
    return _b64(svg)


# --- Rondins gravés (bas de l'écran de connexion) ---------------------------------
_BOIS = [("#F6E2BC", "#DFB985", "#B98A52"), ("#F0D6A8", "#D6A56C", "#AD7C47"),
         ("#EBCB9D", "#CC9A62", "#A2713F"), ("#F8E7C6", "#E2BE86", "#BC8F57")]


def _defs_bois() -> str:
    d = ['<radialGradient id="ecorce" cx=".38" cy=".32" r=".85"><stop offset="0" stop-color="#7A5034"/>'
         '<stop offset=".6" stop-color="#4E321E"/><stop offset="1" stop-color="#2B1A0E"/></radialGradient>',
         '<radialGradient id="lustre" cx=".3" cy=".26" r=".75"><stop offset="0" stop-color="#fff" stop-opacity=".30"/>'
         '<stop offset=".55" stop-color="#fff" stop-opacity=".04"/><stop offset="1" stop-color="#fff" stop-opacity="0"/>'
         '</radialGradient>',
         '<linearGradient id="sol" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#06140D" stop-opacity="0"/>'
         '<stop offset="1" stop-color="#06140D" stop-opacity=".85"/></linearGradient>',
         '<radialGradient id="brume" cx=".5" cy=".5" r=".5"><stop offset="0" stop-color="#E3C592" stop-opacity=".22"/>'
         '<stop offset="1" stop-color="#E3C592" stop-opacity="0"/></radialGradient>']
    for i, (a, b, c) in enumerate(_BOIS):
        d.append(f'<radialGradient id="bois{i}" cx=".42" cy=".38" r=".78"><stop offset="0" stop-color="{a}"/>'
                 f'<stop offset=".55" stop-color="{b}"/><stop offset="1" stop-color="{c}"/></radialGradient>')
    return "".join(d)


def _rondin(cx, cy, r, rnd, sombre=0.0, ombre=True) -> str:
    """Face coupée d'un rondin, façon gravure : écorce, cernes fins irréguliers, cœur, fentes, reflet."""
    ph = _phases(rnd)
    bois = r * .86
    p = []
    if ombre:
        p.append(f'<circle cx="{cx + r * .05:.1f}" cy="{cy + r * .14:.1f}" r="{r * 1.02:.1f}" fill="#020805" '
                 f'opacity=".45" filter="url(#flou2)"/>')
    p.append(f'<path d="{_poly(cx, cy, r, ph, .012)}" fill="url(#ecorce)" stroke="#1A0E06" stroke-width="1.4"/>')
    p.append(f'<path d="{_poly(cx, cy, r * .955, ph, .012)}" fill="none" stroke="#C9A06F" stroke-opacity=".26" '
             f'stroke-width="{r * .05:.1f}" stroke-dasharray="{r * .12:.1f} {r * .07:.1f}"/>')
    p.append(f'<path d="{_poly(cx, cy, bois, ph, .014)}" fill="url(#bois{rnd.randrange(len(_BOIS))})"/>')
    p.append(_cernes(cx, cy, bois * .97, 12, rnd, "#7A4A22", op=(.20, .40), larg=(.6, 1.25), amp=.014, rmin=.07, ph=ph))
    p.append(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{r * .07:.1f}" fill="#8F5A2B" opacity=".55"/>')
    for _ in range(2):
        a = rnd.uniform(0, 6.283)
        p.append(f'<path d="M{cx:.1f} {cy:.1f} Q {cx + math.cos(a + .1) * r * .45:.1f} {cy + math.sin(a + .1) * r * .45:.1f} '
                 f'{cx + math.cos(a - .1) * r * .8:.1f} {cy + math.sin(a - .1) * r * .8:.1f}" stroke="#5A3414" '
                 f'stroke-opacity=".38" stroke-width="1" fill="none" stroke-linecap="round"/>')
    p.append(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{bois:.1f}" fill="url(#lustre)"/>')
    if sombre:
        p.append(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{r:.1f}" fill="#06140D" opacity="{sombre:.2f}"/>')
    return "".join(p)


def art_rondins() -> str:
    """Rangée basse de rondins gravés, fondue dans l'ombre (viewBox 800 × 200)."""
    rnd = random.Random(8)
    rangee = "".join(_rondin(x, 200, rnd.uniform(78, 90), rnd, sombre=.12)
                     for x in (20, 160, 300, 440, 580, 720, 830))
    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 800 200"><defs>{_defs()}{_defs_bois()}</defs>'
           f'<ellipse cx="400" cy="170" rx="380" ry="46" fill="url(#brume)"/>'
           f'{rangee}<rect y="110" width="800" height="90" fill="url(#sol)"/></svg>')
    return _b64(svg)


# --- Emblème, en-tête, filigranes -------------------------------------------------
def art_emblem() -> str:
    """Pastille : cernes dorés d'une section de tronc + une feuille (logo de l'écran de connexion)."""
    rnd = random.Random(3)
    cernes = _cernes(46, 52, 31, 8, rnd, "#E8CB9A", op=(.55, .92), larg=(.9, 1.7), amp=.02, rmin=.10)
    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 96 96"><defs>{_defs()}'
           f'<linearGradient id="pastille" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#1D5A40"/>'
           f'<stop offset="1" stop-color="#0C2A1C"/></linearGradient></defs>'
           f'<circle cx="48" cy="48" r="46" fill="url(#pastille)" stroke="#7FD1A0" stroke-opacity=".55" stroke-width="2"/>'
           f'<circle cx="46" cy="52" r="33" fill="#0E2E20"/>{cernes}'
           f'{_feuille_pleine(52, 56, 38, .36, 1.0)}</svg>')
    return _b64(svg)


def art_feuille_en_tete() -> str:
    rnd = random.Random(5)
    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 240 180"><defs>{_defs()}</defs>'
           f'{_rameau((256, -8), (222, 22), (196, 56), (172, 102), 6, .50, rnd, "#C4EBD0", .62, 1.3, "menthe")}</svg>')
    return _b64(svg)


def art_cernes() -> str:
    """Filigrane plein écran de l'écran de connexion : grands cernes d'arbre, vert menthe + cœur doré (800 × 1400)."""
    rnd = random.Random(4)
    ph = _phases(rnd)
    grand = (_cernes(700, 1170, 640, 34, rnd, "#9FE0B8", op=(.015, .05), larg=(.8, 2.0), ph=ph) +
             _cernes(700, 1170, 230, 11, rnd, "#E6C998", op=(.03, .07), larg=(.8, 1.8), ph=ph))
    haut = _cernes(30, 110, 360, 22, rnd, "#9FE0B8", op=(.012, .04), larg=(.7, 1.6))
    fentes = "".join(
        f'<path d="M700 1170 L{700 + math.cos(a) * 560:.0f} {1170 + math.sin(a) * 560:.0f}" stroke="#9FE0B8" '
        f'stroke-opacity=".035" stroke-width="1.2"/>' for a in (3.5, 4.1, 5.0))
    svg = f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 800 1400">{grand}{haut}{fentes}</svg>'
    return _b64(svg)


def art_fond_clair() -> str:
    """Fond discret de l'application (thème clair) : cernes et feuillage très légers (800 × 1400)."""
    rnd = random.Random(6)
    ph = _phases(rnd)
    cernes = (_cernes(20, 1260, 640, 30, rnd, "#2D6A4F", op=(.025, .075), larg=(.8, 2.0), ph=ph) +
              _cernes(20, 1260, 220, 9, rnd, "#B58A55", op=(.05, .10), larg=(.8, 1.6), ph=ph) +
              _cernes(790, 70, 330, 18, rnd, "#2D6A4F", op=(.02, .06), larg=(.7, 1.6)))
    vert = "#2D6A4F"
    rameaux = (_rameau((830, 330), (700, 360), (610, 460), (570, 600), 8, .85, rnd, vert, .13, 1.4) +
               _rameau((-30, 880), (90, 860), (190, 930), (240, 1050), 7, .8, rnd, vert, .11, 1.4))
    svg = f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 800 1400">{cernes}{rameaux}</svg>'
    return _b64(svg)


def _palme(p0, p1, p2, n, longueur, fill, op):
    """Palme tropicale : nervure courbe (Bézier) + folioles de part et d'autre."""
    def pt(t):
        x = (1 - t) ** 2 * p0[0] + 2 * (1 - t) * t * p1[0] + t * t * p2[0]
        y = (1 - t) ** 2 * p0[1] + 2 * (1 - t) * t * p1[1] + t * t * p2[1]
        dx = 2 * (1 - t) * (p1[0] - p0[0]) + 2 * t * (p2[0] - p1[0])
        dy = 2 * (1 - t) * (p1[1] - p0[1]) + 2 * t * (p2[1] - p1[1])
        return x, y, math.atan2(dy, dx)
    out = [f'<path d="M{p0[0]:.1f},{p0[1]:.1f} Q{p1[0]:.1f},{p1[1]:.1f} {p2[0]:.1f},{p2[1]:.1f}" stroke="{fill}" '
           f'stroke-width="2.4" fill="none" stroke-opacity="{op}"/>']
    for i in range(n):
        t = .12 + .86 * i / (n - 1)
        x, y, a = pt(t)
        ln = longueur * math.sin(math.pi * (.15 + .85 * (1 - t) ** .8)) * (1 - .45 * t) + 8
        for sg in (1, -1):
            ang = a + sg * math.radians(62 - 18 * t)
            ex, ey = x + ln * math.cos(ang), y + ln * math.sin(ang)
            mx, my = (x + ex) / 2, (y + ey) / 2
            nx, ny = -math.sin(ang), math.cos(ang)
            w = ln * .17
            out.append(f'<path d="M{x:.1f},{y:.1f} Q{mx + nx * w:.1f},{my + ny * w:.1f} {ex:.1f},{ey:.1f} '
                       f'Q{mx - nx * w:.1f},{my - ny * w:.1f} {x:.1f},{y:.1f}Z" fill="{fill}" fill-opacity="{op}"/>')
    return "".join(out)


def art_feuillage() -> str:
    """Fond plein écran de la connexion : feuillage dense de palmes tropicales (390 × 844, recadré en 'cover')."""
    w, h, n = 390, 844, 46
    pal = ("#0F3A2B", "#17503A", "#1F6A4A", "#2D8A5F", "#3FA074", "#5DB98A")
    rnd = random.Random(11)
    s = f'<rect width="{w}" height="{h}" fill="#0E3426"/>'
    for i in range(n):
        cote = rnd.choice("tblr")
        if cote == "t":
            p0, ang = (rnd.uniform(-20, w + 20), -15), rnd.uniform(60, 120)
        elif cote == "b":
            p0, ang = (rnd.uniform(-20, w + 20), h + 15), rnd.uniform(-120, -60)
        elif cote == "l":
            p0, ang = (-15, rnd.uniform(0, h)), rnd.uniform(-40, 40)
        else:
            p0, ang = (w + 15, rnd.uniform(0, h)), rnd.uniform(140, 220)
        ln = rnd.uniform(.45, .85) * h * .55
        a = math.radians(ang + rnd.uniform(-25, 25))
        p2 = (p0[0] + ln * math.cos(a), p0[1] + ln * math.sin(a))
        c = rnd.uniform(-.35, .35)
        mid = ((p0[0] + p2[0]) / 2 - (p2[1] - p0[1]) * c, (p0[1] + p2[1]) / 2 + (p2[0] - p0[0]) * c)
        col = pal[i * len(pal) // n if rnd.random() < .6 else rnd.randrange(len(pal))]
        s += _palme(p0, mid, p2, rnd.randint(13, 19), rnd.uniform(46, 74), col, .92)
    return _b64(f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w} {h}" preserveAspectRatio="xMidYMid slice">{s}</svg>')


def art_emblem_ivoire() -> str:
    """Logo : cernes ivoire d'une section de tronc + feuille terracotta."""
    rnd = random.Random(2)
    cernes = "".join(
        '<polygon points="' + " ".join(
            f"{37 + (5 + i * 5.2) * (1 + .05 * math.sin(3 * a + i * .5) + .03 * math.sin(5 * a + i)) * math.cos(a):.1f},"
            f"{37 + (5 + i * 5.2) * (1 + .05 * math.sin(3 * a + i * .5) + .03 * math.sin(5 * a + i)) * math.sin(a):.1f}"
            for a in (k / 60 * 2 * math.pi for k in range(60)))
        + '" fill="none" stroke="#FBF6EA" stroke-opacity=".9" stroke-width="1.6"/>' for i in range(5))
    svg = ('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 74 74">'
           '<circle cx="37" cy="37" r="35" fill="none" stroke="#FBF6EA" stroke-opacity=".5" stroke-width="1.5"/>'
           f'{cernes}<circle cx="37" cy="37" r="2.5" fill="#E58A63"/>'
           '<path d="M44 14 C60 18 62 34 52 42 C42 40 38 24 44 14Z" fill="#E58A63"/>'
           '<path d="M45 18 C50 26 51 33 52 41" stroke="#FBF6EA" stroke-opacity=".6" fill="none"/></svg>')
    return _b64(svg)


@st.cache_resource(show_spinner=False)
def arts() -> dict:
    return {"feuilles": art_feuilles(), "rondins": art_rondins(), "emblem": art_emblem(),
            "entete": art_feuille_en_tete(), "cernes": art_cernes(), "fond": art_fond_clair(),
            "feuillage": art_feuillage(), "emblem_ivoire": art_emblem_ivoire()}


# ---------------------------------------------------------------------------
# Style — palette forêt / bois, thème clair, pensé pour téléphone
# ---------------------------------------------------------------------------
CSS = """
<style>
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&family=Fraunces:opsz,wght@9..144,600;9..144,700&display=swap');
:root{
  --bg:#F1F6EF; --surface:#FFFFFF; --alt:#F4F8F2; --border:#D3DFD3; --text:#14251C;
  --muted:#5A6F60; --accent:#2D6A4F; --accent2:#40916C; --soft:#E3EFE5; --deep:#123524;
  --wood:#8A5A44; --sand:#EADBC0; --danger:#B94A44; --warn:#B7791F;
}
html, body, .stApp, [class*="css"]{ font-family:'Inter', system-ui, -apple-system, 'Segoe UI', sans-serif; }
.stApp{ background:var(--bg); color:var(--text); }
header[data-testid="stHeader"], footer, #MainMenu, [data-testid="stToolbar"]{ display:none !important; }
.block-container{ padding:1.1rem .95rem 4rem !important; max-width:720px; }
h1,h2,h3{ letter-spacing:-.01em; }


/* Interrupteur En ligne <-> Terrain */
.m4-hero-row{ display:flex; align-items:center; justify-content:space-between; gap:.6rem; flex-wrap:wrap; }
.m4-sw{ display:inline-flex; align-items:center; gap:.5rem; text-decoration:none !important; color:#fff !important; font-size:.72rem; font-weight:800; letter-spacing:.02em; }
.m4-sw .rail{ position:relative; width:54px; height:27px; border-radius:99px; background:linear-gradient(90deg,#7BD443,#3FBF2A);
  box-shadow:inset 0 2px 5px rgba(0,0,0,.3), 0 1px 0 rgba(255,255,255,.18); }
.m4-sw .kn{ position:absolute; top:2.5px; left:2.5px; width:22px; height:22px; border-radius:50%;
  background:radial-gradient(circle at 35% 30%,#bdbdbd,#8a8a8a 70%); box-shadow:0 2px 5px rgba(0,0,0,.4), inset 0 0 0 2px rgba(255,255,255,.35);
  transition:left .35s cubic-bezier(.3,.7,.2,1); }
.m4-sw:hover .kn, .m4-sw:active .kn, .m4-sw:focus .kn{ left:29.5px; }
.m4-sw.off{ opacity:.55; pointer-events:none; }
.m4-sw.vieux .rail{ background:linear-gradient(90deg,#F2B04C,#E58A2B); }
.m4-sw-note{ font-size:.7rem; color:#FFE3B0; margin-top:.35rem; }

/* En-tête (cernes d'arbre + feuillage) */
.m4-hero{ position:relative; overflow:hidden; border-radius:20px; padding:1rem 1rem .95rem; margin:.1rem 0 .95rem; color:#fff;
  background:
    repeating-radial-gradient(circle at 106% -30%, rgba(255,255,255,.075) 0 2px, transparent 2px 13px),
    linear-gradient(135deg,#0F2D1F 0%,#1B4332 55%,#2D6A4F 100%);
  box-shadow:0 12px 26px rgba(18,53,36,.24); }
.m4-hero::after{ content:""; position:absolute; right:-4px; top:-6px; width:150px; height:112px;
  background:url("__ENTETE__") no-repeat right top / contain; pointer-events:none; }
.m4-hero-in{ position:relative; z-index:1; display:flex; flex-direction:column; gap:.55rem; }
.m4-brand{ font-family:'Fraunces', Georgia, serif; font-size:1.55rem; font-weight:700; letter-spacing:-.01em; line-height:1.05; }
.m4-brand small{ display:block; font-family:'Inter',system-ui,sans-serif; font-size:.74rem; font-weight:500;
  color:#B7E4C7; letter-spacing:0; margin-top:.25rem; }
.m4-chip{ align-self:flex-start; font-size:.72rem; font-weight:600; padding:.34rem .7rem; border-radius:999px;
  background:rgba(255,255,255,.14); color:#E7F6EB; border:1px solid rgba(255,255,255,.28); white-space:nowrap; }
.m4-chip.old{ background:#FBEFD9; color:#8A5B12; border-color:#EBD3A2; }

/* Cartes chiffres clés */
.m4-kpis{ display:grid; grid-template-columns:1fr 1fr; gap:10px; margin:.2rem 0 1rem; }
.m4-kpi{ background:var(--surface); border:1px solid var(--border); border-radius:16px; padding:.8rem .9rem .85rem;
         border-bottom:3px solid var(--c, var(--accent)); box-shadow:0 1px 2px rgba(18,53,36,.05); }
.m4-kpi .l{ font-size:.68rem; font-weight:600; text-transform:uppercase; letter-spacing:.06em; color:var(--muted); }
.m4-kpi .v{ font-size:1.42rem; font-weight:700; line-height:1.15; margin-top:.2rem; font-variant-numeric:tabular-nums; }
.m4-kpi .v{ color:var(--text); }
.m4-kpi .v small{ font-size:.75rem; font-weight:500; color:var(--muted); margin-left:.15rem; }
.m4-kpi .s{ font-size:.72rem; color:var(--muted); margin-top:.15rem; }
.m4-kpis.three{ grid-template-columns:1fr 1fr 1fr; }
.m4-kpis.three .m4-kpi .v{ font-size:1.05rem; }
.m4-sec{ font-size:.76rem; font-weight:700; text-transform:uppercase; letter-spacing:.08em; color:var(--muted); margin:1.15rem 0 .5rem; }

/* Répartition (barre empilée) */
.m4-stack{ display:flex; height:16px; border-radius:99px; overflow:hidden; background:var(--soft); }
.m4-stack i{ display:block; height:100%; }
.m4-legend{ display:flex; flex-wrap:wrap; gap:6px 12px; margin-top:.65rem; }
.m4-legend span{ font-size:.74rem; color:var(--muted); display:inline-flex; align-items:center; gap:5px; }
.m4-legend b{ color:var(--text); font-weight:600; }
.m4-dot{ width:10px; height:10px; border-radius:50%; flex:none; display:inline-block; }

/* Cartes de rapport (dépliables sans recharger la page) */
.m4-total{ border-radius:18px; padding:.9rem .95rem .85rem; margin:.1rem 0 .8rem; color:#fff;
  background:repeating-radial-gradient(circle at 108% 120%, rgba(255,255,255,.06) 0 2px, transparent 2px 12px),
             linear-gradient(135deg,#123524,#2D6A4F);
  box-shadow:0 10px 22px rgba(18,53,36,.2); }
.m4-total-h{ display:flex; justify-content:space-between; align-items:baseline; gap:8px; margin-bottom:.45rem; }
.m4-total-h b{ font-size:.78rem; text-transform:uppercase; letter-spacing:.08em; color:#B7E4C7; }
.m4-total-h span{ font-size:.72rem; color:#CDEBD6; text-align:right; }
.m4-card{ background:var(--surface); border:1px solid var(--border); border-radius:16px; margin-bottom:10px; overflow:hidden;
  box-shadow:0 1px 2px rgba(18,53,36,.05); }
.m4-card summary{ list-style:none; cursor:pointer; padding:.8rem .9rem .75rem; display:block; -webkit-tap-highlight-color:transparent; }
.m4-card summary::-webkit-details-marker{ display:none; }
.m4-card[open] > summary{ background:linear-gradient(#F6FAF4,#FFFFFF); border-bottom:1px solid var(--border); }
.m4-card-top{ display:flex; align-items:center; gap:8px; margin-bottom:.55rem; }
.m4-card-top b{ font-weight:650; font-size:.98rem; line-height:1.2; }
.m4-card-vol{ margin-left:auto; text-align:right; font-weight:700; font-variant-numeric:tabular-nums; white-space:nowrap; }
.m4-card-vol small{ font-weight:500; color:var(--muted); font-size:.7rem; }
.m4-chev{ width:7px; height:7px; border-right:2px solid var(--muted); border-bottom:2px solid var(--muted);
  transform:rotate(45deg); transition:transform .2s; margin:0 2px 3px 6px; flex:none; }
.m4-card[open] .m4-chev{ transform:rotate(-135deg); margin-bottom:-2px; }
.m4-body{ padding:.55rem .9rem .75rem; background:var(--alt); }
.m4-body-h{ font-size:.68rem; font-weight:700; text-transform:uppercase; letter-spacing:.07em; color:var(--muted); margin:.1rem 0 .45rem; }
.m4-sub{ background:var(--surface); border:1px solid var(--border); border-radius:12px; padding:.55rem .7rem .6rem; margin-bottom:7px; }
.m4-sub-top{ display:flex; align-items:center; gap:7px; font-size:.86rem; }
.m4-sub-top b{ font-weight:600; }
.m4-sub-top span.v{ margin-left:auto; font-weight:700; font-variant-numeric:tabular-nums; white-space:nowrap; }
.m4-sub .m4-gauge{ height:5px; background:var(--soft); border-radius:99px; margin:.4rem 0 .3rem; overflow:hidden; }
.m4-sub .m4-gauge i{ display:block; height:100%; border-radius:99px; }
.m4-ess-sub{ font-size:.72rem; color:var(--muted); line-height:1.4; }

/* Étapes : abattu → billonné → évacué → usiné */
.m4-pipe{ display:grid; gap:5px; }
.m4-pl{ display:grid; grid-template-columns:3.7rem 1fr 5.6rem; align-items:center; gap:8px; font-size:.72rem; }
.m4-pl-l{ color:var(--muted); font-weight:500; }
.m4-pl-t{ height:7px; background:var(--soft); border-radius:99px; overflow:hidden; }
.m4-pl-t i{ display:block; height:100%; border-radius:99px; }
.m4-pl-v{ text-align:right; font-weight:600; font-variant-numeric:tabular-nums; }
.m4-total .m4-pl-l{ color:#B7E4C7; }
.m4-total .m4-pl-t{ background:rgba(255,255,255,.16); }
.m4-total .m4-pl-v{ color:#fff; }
.m4-chips{ display:flex; flex-wrap:wrap; gap:6px; margin-top:.6rem; }
.m4-c{ font-size:.7rem; font-weight:600; padding:.2rem .55rem; border-radius:999px; border:1px solid transparent; white-space:nowrap; }
.m4-c.bad{ background:#F7E1DF; color:#9B3A35; border-color:#E8BDB9; }
.m4-c.warn{ background:#FBEFD9; color:#8A5B12; border-color:#EBD3A2; }
.m4-c.ok{ background:#E3F0E8; color:#2D6A4F; border-color:#C5DFD0; }
.m4-c.wood{ background:#F1E6D2; color:#6B4630; border-color:#E0CDA9; }
.m4-total .m4-c{ background:rgba(255,255,255,.14); color:#fff; border-color:rgba(255,255,255,.26); }
.m4-pl.on .m4-pl-l{ color:var(--text); font-weight:700; }
.m4-pl.on .m4-pl-v{ font-weight:800; }
.m4-pl.on .m4-pl-t{ background:#CFE3D6; }
.m4-total .m4-pl.on .m4-pl-l{ color:#fff; }
.m4-total .m4-pl.on .m4-pl-t{ background:rgba(255,255,255,.28); }
.m4-rank{ font-size:.66rem; font-weight:700; color:var(--accent); background:var(--soft); border-radius:999px;
  padding:.12rem .45rem; min-width:1.45rem; text-align:center; flex:none; }
/* Évacuation : LV, billes, camions */
.m4-evk{ display:grid; grid-template-columns:1fr 1fr; gap:8px; margin:.1rem 0 .15rem; }
.m4-evk > div{ background:rgba(255,255,255,.12); border:1px solid rgba(255,255,255,.2); border-radius:12px; padding:.5rem .7rem .55rem; }
.m4-evk b{ display:block; font-size:1.18rem; font-weight:700; color:#fff; font-variant-numeric:tabular-nums; line-height:1.2; }
.m4-evk span{ font-size:.64rem; text-transform:uppercase; letter-spacing:.07em; color:#DDF3E5; font-weight:600; }
.m4-note{ font-size:.72rem; color:#CDEBD6; margin-top:.55rem; }
.m4-gauge2{ height:6px; background:var(--soft); border-radius:99px; overflow:hidden; margin:.5rem 0 .1rem; }
.m4-gauge2 i{ display:block; height:100%; border-radius:99px; }
.m4-lvs{ display:flex; flex-wrap:wrap; gap:5px; margin:.1rem 0 .15rem; }
.m4-lvs span{ font-size:.7rem; font-weight:600; background:var(--surface); border:1px solid var(--border); color:var(--text);
  padding:.14rem .48rem; border-radius:8px; font-variant-numeric:tabular-nums; }
.m4-lvs span.plus{ background:transparent; border-style:dashed; color:var(--muted); }
.m4-resume{ font-size:.78rem; color:var(--muted); margin:.1rem 0 .6rem; line-height:1.45; }
.m4-resume b{ color:var(--text); }

/* Matrice essence × titre */
.m4-mx-wrap{ overflow-x:auto; border:1px solid var(--border); border-radius:14px; background:var(--surface); -webkit-overflow-scrolling:touch; }
table.m4-mx{ border-collapse:separate; border-spacing:0; font-size:.72rem; font-variant-numeric:tabular-nums; min-width:100%; }
.m4-mx th, .m4-mx td{ padding:.42rem .5rem; border-bottom:1px solid #E6EEE6; white-space:nowrap; }
.m4-mx thead th{ background:var(--soft); color:var(--muted); font-weight:700; font-size:.66rem; text-transform:uppercase;
  letter-spacing:.04em; text-align:right; position:sticky; top:0; }
.m4-mx .r{ position:sticky; left:0; z-index:2; background:var(--surface); text-align:left; font-weight:600;
  white-space:normal; min-width:118px; max-width:150px; border-right:1px solid var(--border); }
.m4-mx thead .r{ background:var(--soft); z-index:3; }
.m4-mx td.n{ text-align:right; min-width:76px; }
.m4-mx tr.t td, .m4-mx tr.t th{ font-weight:700; background:var(--soft); }
.m4-mx td.tt{ font-weight:700; border-left:1px solid var(--border); }
/* Bilan par titre et essence (Aperçu) */
table.m4-bt{ min-width:100%; font-size:.64rem; }
.m4-bt th, .m4-bt td{ padding:.32rem .3rem; }
.m4-bt thead th{ font-size:.56rem; letter-spacing:.02em; }
.m4-bt td.n{ min-width:0; }
.m4-bt td.tl{ position:sticky; left:0; z-index:2; width:26px; min-width:26px; max-width:26px; padding:.5rem 0 !important; text-align:center;
  background:var(--deep); color:#fff; font-weight:700; font-size:.64rem; letter-spacing:.08em; writing-mode:vertical-rl;
  border-bottom:1px solid rgba(255,255,255,.18); }
.m4-bt td.tl span{ display:inline-block; transform:rotate(180deg); }
.m4-bt .r{ left:26px; min-width:62px; max-width:96px; }
.m4-bt thead th:first-child{ position:sticky; left:0; z-index:4; width:26px; min-width:26px; padding:0 !important; }
.m4-bt thead .r{ left:26px; }
.m4-bt td.neg{ color:var(--danger); font-weight:700; }
.m4-bt tr.t td{ border-top:1px solid var(--border); }
.m4-bt tr.g td{ background:var(--deep); color:#fff; font-weight:700; }
.m4-bt tr.g td.r{ background:var(--deep); }
.m4-bt tr.g td.neg{ color:#FFB4AE; }
.m4-bt th.sg{ background:var(--accent2) !important; color:#fff !important; text-align:center; letter-spacing:.06em; }
.m4-bt-big thead th{ text-align:center; vertical-align:middle; }
.m4-bt-big thead tr:nth-child(2) th:first-child{ position:static; width:auto; min-width:0; padding:.32rem .3rem !important; left:auto; }
.m4-bt-big th.sg2{ background:var(--soft); }
.m4-bt-big td.tt{ border-left:1px solid var(--border); }
.m4-bt-pc{ display:none; }
@media (min-width:980px){ .m4-bt-cartes{ display:none; } .m4-bt-pc{ display:block; } }
/* Bilan en cartes (téléphone) */
.bc-card{ background:var(--surface); border:1px solid var(--border); border-radius:16px; overflow:hidden; margin-bottom:.8rem; }
details.bc-card > summary{ list-style:none; cursor:pointer; }
details.bc-card > summary::-webkit-details-marker{ display:none; }
.bc-h{ display:flex; justify-content:space-between; align-items:center; gap:.6rem; padding:.7rem .85rem; background:var(--soft); }
.bc-h > div{ flex:1; min-width:0; }
.bc-h b{ font-size:.95rem; }
.bc-h small{ display:block; color:var(--muted); font-size:.64rem; margin-top:.12rem; }
details.bc-card > summary .bc-h::after{ content:"▾"; color:var(--muted); font-size:.9rem; transition:transform .2s; }
details.bc-card[open] > summary .bc-h::after{ transform:rotate(180deg); }
.bc-card.gen .bc-h{ background:var(--deep); color:#fff; }
.bc-card.gen .bc-h small{ color:#CFE3D6; }
.bc-pill{ font-size:.68rem; font-weight:700; padding:.22rem .6rem; border-radius:999px; background:rgba(64,145,108,.18); color:var(--accent); white-space:nowrap; }
.bc-card.gen .bc-pill{ background:rgba(255,255,255,.16); color:#fff; }
.bc-pill.red{ background:rgba(185,74,68,.18); color:var(--danger); }
.bc-card.gen .bc-pill.red{ background:rgba(255,180,174,.22); color:#FFB4AE; }
.bc-ess{ padding:.75rem .85rem; border-top:1px solid var(--border); }
.bc-l1{ display:flex; justify-content:space-between; align-items:center; gap:.5rem; }
.bc-nm{ display:flex; align-items:center; gap:.45rem; font-weight:700; font-size:.84rem; }
.bc-nm i{ width:.55rem; height:.55rem; border-radius:50%; display:inline-block; }
.bc-pieds{ font-size:.7rem; color:var(--muted); }
.bc-pieds b{ color:var(--text); font-size:.84rem; }
.bc-pieds.red, .bc-pieds.red b{ color:var(--danger); }
.bc-bar{ height:6px; border-radius:9px; background:var(--soft); overflow:hidden; margin:.4rem 0 .6rem; }
.bc-bar i{ display:block; height:100%; background:var(--accent2); border-radius:9px; }
.bc-bar.red i{ background:var(--danger); }
.bc-stats{ display:grid; grid-template-columns:repeat(4,1fr); gap:.25rem; margin:.5rem 0; }
.bc-st{ background:var(--soft); border-radius:10px; padding:.35rem .1rem; text-align:center; }
.bc-st span{ display:block; font-size:.52rem; text-transform:uppercase; letter-spacing:.04em; color:var(--muted); }
.bc-st b{ font-size:.64rem; font-variant-numeric:tabular-nums; }
.bc-st b.neg{ color:var(--danger); }
.bc-sites{ border:1px solid var(--border); border-radius:12px; overflow:hidden; }
.bc-sl{ display:grid; grid-template-columns:1.2fr 1fr 1fr 1fr; align-items:center; gap:.2rem; padding:.32rem .6rem; font-size:.68rem; border-top:1px solid var(--border); }
.bc-sl:first-child{ border-top:0; }
.bc-sl > span{ font-weight:700; letter-spacing:.03em; }
.bc-sl > b{ text-align:right; font-variant-numeric:tabular-nums; font-weight:600; }
.bc-sl.hd{ background:linear-gradient(90deg,var(--deep),var(--accent2)); color:#fff; font-size:.56rem; text-transform:uppercase; letter-spacing:.08em; padding:.26rem .6rem; }
.bc-sl.hd > b, .bc-sl.hd > span{ font-weight:800; }
.bc-sl.tot{ background:var(--soft); }
.bc-sl.tot > span, .bc-sl.tot > b{ font-weight:800; }
.bc-aucun{ font-size:.68rem; color:var(--muted); font-style:italic; padding:.15rem 0; }
.bc-pied{ display:flex; justify-content:space-between; gap:.6rem; padding:.55rem .85rem; background:var(--soft); font-size:.7rem; border-top:1px solid var(--border); }
.bc-card.gen .bc-pied{ border-top:0; }

.m4-badge{ display:inline-block; font-size:.7rem; font-weight:600; padding:.18rem .55rem; border-radius:999px; border:1px solid transparent; }
.m4-badge.ok{ background:#E3F0E8; color:#2D6A4F; border-color:#C5DFD0; }
.m4-badge.warn{ background:#FBEFD9; color:#8A5B12; border-color:#EBD3A2; }
.m4-badge.bad{ background:#F7E1DF; color:#9B3A35; border-color:#E8BDB9; }
.m4-badge.neutral{ background:#EAF0EC; color:#52695C; border-color:#D5E0D8; }
.m4-fiche-t{ display:flex; align-items:center; gap:8px; flex-wrap:wrap; margin-bottom:.15rem; }
.m4-fiche-t b{ font-size:1.05rem; }
.m4-fiche-s{ font-size:.78rem; color:var(--muted); margin-bottom:.5rem; }
.m4-chaine{ position:relative; padding:.2rem 0 .1rem; }
.m4-et{ position:relative; display:flex; gap:.75rem; padding-bottom:.9rem; }
.m4-et:not(:last-child)::before{ content:""; position:absolute; left:.95rem; top:2rem; bottom:.1rem; width:2px; background:var(--line,#D3DFD3); }
.m4-et-pt{ flex:0 0 1.9rem; height:1.9rem; border-radius:50%; display:flex; align-items:center; justify-content:center; font-weight:800;
  font-size:.82rem; color:#fff; background:#2D6A4F; box-shadow:0 2px 6px rgba(20,37,28,.22); }
.m4-et.warn .m4-et-pt{ background:#C9822B; } .m4-et.bad .m4-et-pt{ background:#B94A44; }
.m4-et.vide .m4-et-pt{ background:transparent; color:var(--muted); border:2px dashed #9DB3A3; box-shadow:none; }
.m4-et-c{ flex:1; min-width:0; }
.m4-et-t{ display:flex; flex-wrap:wrap; align-items:baseline; justify-content:space-between; gap:.1rem .6rem; font-weight:800; font-size:.95rem; }
.m4-et-t span{ font-weight:600; font-size:.74rem; color:var(--muted); }
.m4-ctl{ display:flex; flex-direction:column; gap:.15rem; border-radius:14px; padding:.8rem 1rem; margin:.6rem 0; color:#fff; box-shadow:0 4px 12px rgba(20,37,28,.22); }
.m4-ctl b{ font-size:1.05rem; letter-spacing:.01em; } .m4-ctl span{ font-size:.8rem; opacity:.92; }
.m4-ctl.ok{ background:linear-gradient(135deg,#2D6A4F,#3D8B66); } .m4-ctl.mid{ background:linear-gradient(135deg,#B5701F,#D08A33); }
.m4-ctl.ko{ background:linear-gradient(135deg,#A8393A,#C4524F); }
.m4-lv-es{ margin:.2rem 0 .5rem; }
.m4-lv-e{ display:flex; gap:.6rem; align-items:baseline; font-size:.86rem; padding:.2rem 0; border-bottom:1px dashed var(--border); }
.m4-lv-e span:first-child{ font-weight:800; min-width:5.2rem; } .m4-lv-e span:nth-child(2){ color:var(--muted); flex:1; } .m4-lv-e b{ font-variant-numeric:tabular-nums; }
.m4-lv-w{ overflow-x:auto; }
.m4-lv-t{ width:100%; border-collapse:collapse; font-size:.74rem; font-variant-numeric:tabular-nums; }
.m4-lv-t th{ text-align:left; font-weight:700; color:var(--muted); padding:.25rem .3rem; border-bottom:2px solid var(--border); white-space:nowrap; }
.m4-lv-t td{ padding:.28rem .3rem; border-bottom:1px solid var(--border); white-space:nowrap; }
.m4-lv-t tr:nth-child(even) td{ background:var(--alt); }
.m4-et-l{ font-size:.86rem; line-height:1.45; margin-top:.1rem; word-break:break-word; }
.m4-copy{ text-align:center; font-size:.68rem; letter-spacing:.04em; color:#9FCFB0; opacity:.55; margin-top:.5rem; }
.m4-copy.clair{ color:#5C7A68; opacity:.6; margin:2rem 0 .6rem; }
.m4-vide{ text-align:center; color:var(--muted); padding:1.6rem .5rem; font-size:.9rem; }
.m4-filtres{ display:flex; flex-wrap:wrap; gap:6px; margin:.2rem 0 .7rem; }
.m4-filtres span{ font-size:.72rem; font-weight:600; background:var(--soft); color:var(--accent); border:1px solid var(--border);
  padding:.22rem .6rem; border-radius:999px; }

/* Widgets Streamlit */
[role="tablist"]{ gap:4px; background:var(--soft); border-radius:14px; padding:4px; border-bottom:0 !important; box-shadow:none !important; }
div:has(> [role="tablist"]){ border-bottom:0 !important; box-shadow:none !important; }
[role="tab"]{ height:40px; border-radius:10px; font-weight:600; color:var(--muted); padding:0 .6rem; flex:1; justify-content:center; }
[role="tab"] p{ color:var(--muted); font-weight:600; font-size:.92rem; }
[role="tab"][aria-selected="true"]{ background:var(--surface); box-shadow:0 1px 2px rgba(18,53,36,.12); }
[role="tab"][aria-selected="true"] p{ color:var(--accent); }
.react-aria-SelectionIndicator, [data-baseweb="tab-highlight"], [data-baseweb="tab-border"]{ display:none !important; }
[data-testid="stElementContainer"]:has(> [data-testid="stButtonGroup"]){ width:100% !important; }
[data-testid="stButtonGroup"]{ width:100%; }
[data-testid="stButtonGroup"] [role="radiogroup"]{ display:flex !important; width:100% !important; max-width:100% !important; gap:4px;
  background:var(--surface); padding:4px; border:1px solid var(--border); border-radius:14px; box-sizing:border-box; }
[data-testid="stButtonGroup"] button[role="radio"]{ flex:1 1 0 !important; min-width:0 !important; width:auto !important; border:0;
  background:transparent; border-radius:10px; min-height:38px; padding:0 .25rem; }
[data-testid="stButtonGroup"] button[role="radio"] div, [data-testid="stButtonGroup"] button[role="radio"] span{ max-width:none !important; }
[data-testid="stButtonGroup"] button[role="radio"] p{ font-size:min(.8rem, 3.3vw); font-weight:600; color:var(--muted); white-space:nowrap; }
[data-testid="stButtonGroup"] button[aria-checked="true"]{ background:linear-gradient(135deg,#2D6A4F,#347A5B); box-shadow:0 4px 10px rgba(45,106,79,.28); }
[data-testid="stButtonGroup"] button[aria-checked="true"] p{ color:#fff; }
[data-testid="stHorizontalBlock"]{ flex-wrap:nowrap !important; gap:.5rem !important; }
[data-testid="stColumn"]{ min-width:0 !important; }
.stButton>button, .stFormSubmitButton>button, .stDownloadButton>button{ border-radius:12px; font-weight:600; border:1px solid var(--border); min-height:2.6rem; }
.stButton>button[kind="primary"], .stFormSubmitButton>button[kind="primary"],
button[data-testid="stBaseButton-primary"], button[data-testid="stBaseButton-primaryFormSubmit"]{
  background:linear-gradient(135deg,#2D6A4F,#347A5B); border:0; color:#fff; box-shadow:0 6px 14px rgba(45,106,79,.28); }
.stButton>button[kind="primary"]:hover, button[data-testid="stBaseButton-primary"]:hover{ filter:brightness(1.07); color:#fff; }
div[data-baseweb="input"], div[data-baseweb="base-input"], div[data-baseweb="select"]>div, textarea{ border-radius:12px !important; }
div[data-testid="stExpander"]{ background:var(--surface); border:1px solid var(--border); border-radius:14px; }
div[data-testid="stExpander"] summary{ font-weight:600; }
div[data-testid="stVerticalBlockBorderWrapper"]{ border-radius:16px; }
div[data-testid="stDataFrame"]{ border-radius:12px; overflow:hidden; border:1px solid var(--border); }


/* --- Améliorations Ergonomiques Mobile --- */
@media (max-width:979px){
  .block-container{ padding-bottom:5.2rem !important; }
  div[data-testid="stTabs"] > div:first-child{
    position:fixed !important; bottom:0; left:0; right:0; z-index:999;
    background:var(--surface); border-top:1px solid var(--border);
    padding:.35rem .4rem calc(.35rem + env(safe-area-inset-bottom));
    box-shadow:0 -4px 16px rgba(0,0,0,.12);
  }
  div[data-testid="stTabs"] [role="tablist"]{ background:transparent; padding:0; gap:2px; }
  div[data-testid="stTabs"] [role="tab"]{ height:44px; padding:0 .25rem; flex-direction:column; gap:2px; }
  div[data-testid="stTabs"] [role="tab"] p{ font-size:min(.72rem, 2.9vw) !important; }
}

/* En-tête responsive : barre d'actions alignée proprement sans superposition */
.m4-actions-bar{ display:flex; justify-content:flex-end; align-items:center; gap:8px; margin-bottom:.45rem; }
[data-testid="stElementContainer"]:has([data-testid="stPopover"]){ position:static !important; height:auto !important; }
[data-testid="stPopover"]{ position:static !important; }
[data-testid="stPopover"] button{ background:var(--surface) !important; border:1px solid var(--border) !important; color:var(--text) !important; }
[data-testid="stPopover"] button span{ color:var(--text) !important; }

.st-key-btn_partage, .st-key-btn_journal, .st-key-btn_alertes{ position:static !important; height:auto !important; width:auto !important; }
.st-key-btn_partage button, .st-key-btn_journal button, .st-key-btn_alertes button{
  position:static !important; width:auto !important; height:38px !important; padding:0 .75rem !important;
  border-radius:12px !important; display:inline-flex !important; align-items:center; gap:5px;
}
.st-key-btn_partage button p, .st-key-btn_journal button p, .st-key-btn_alertes button p{
  display:inline !important; font-size:.78rem !important; margin:0 !important;
}

/* Cartes mobiles pour les billes filles dans Rechercher */
.m4-bille-cards{ display:grid; gap:8px; margin-top:.4rem; }
.m4-bille-card{ background:var(--alt); border:1px solid var(--border); border-radius:12px; padding:.6rem .75rem; font-size:.78rem; }
.m4-bille-card.exact{ background:#D8F3DC; border-color:#2D6A4F; border-width:2px; }
.m4-bille-head{ display:flex; justify-content:space-between; align-items:center; font-weight:700; margin-bottom:.25rem; }
.m4-bille-meta{ color:var(--muted); font-size:.72rem; line-height:1.45; }
.m4-copy-chip{ cursor:pointer; background:var(--surface); border:1px solid var(--border); border-radius:6px;
  padding:.1rem .4rem; font-family:monospace; font-size:.75rem; display:inline-flex; align-items:center; gap:4px; }
.m4-copy-chip:active{ background:var(--soft); transform:scale(.96); }
@media (min-width:768px){ .m4-bille-cards{ display:none; } }
@media (max-width:767px){ .m4-bille-table-pc{ display:none; } }

/* Bandeau brouillon sauvegardé */
.m4-draft-banner{ background:var(--soft); border:1px solid var(--accent2); color:var(--accent);
  border-radius:12px; padding:.5rem .8rem; font-size:.78rem; font-weight:600; margin:.35rem 0 .65rem;
  display:flex; align-items:center; justify-content:space-between; }

/* Bouton réglages */
[data-testid="stElementContainer"]:has([data-testid="stPopover"]){ position:relative; height:0; z-index:30; overflow:visible; }
[data-testid="stPopover"]{ position:absolute; z-index:30; top:3.75rem; right:.65rem; width:auto !important; }
[data-testid="stPopover"] button{ width:38px; height:38px; min-height:0 !important; padding:0 !important; border-radius:50% !important;
  background:rgba(255,255,255,.16) !important; border:1px solid rgba(255,255,255,.34) !important; color:#fff !important;
  -webkit-backdrop-filter:blur(4px); backdrop-filter:blur(4px); box-shadow:none !important; justify-content:center; }
[data-testid="stPopover"] button p{ display:none; }
[data-testid="stPopover"] button span{ color:#fff !important; }
[data-testid="stPopover"] button svg{ display:none !important; }
[data-testid="stPopover"] button > div > div:last-child{ display:none !important; }
[data-testid="stPopoverBody"]{ width:min(92vw, 400px) !important; max-width:92vw !important; border-radius:18px !important;
  box-shadow:0 18px 40px rgba(18,53,36,.28) !important; }
/* Bouton Partager : pastille terracotta à gauche de l'engrenage */
.st-key-btn_partage{ position:relative; width:100% !important; height:0; z-index:30; overflow:visible; }
.st-key-btn_partage button{ position:absolute; top:.7rem; right:2.6rem; width:38px; height:38px; min-height:0 !important;
  padding:0 !important; border-radius:50% !important; justify-content:center;
  background:linear-gradient(135deg,#d0764a,#b5532f) !important; border:1px solid rgba(255,255,255,.5) !important;
  color:#fff !important; box-shadow:0 5px 14px rgba(120,50,20,.35) !important; }
.st-key-btn_partage button p{ display:none; }
/* Pastille Journal (administrateurs) : verre dépoli, à gauche du bouton Partager */
.st-key-btn_journal{ position:relative; width:100% !important; height:0; z-index:30; overflow:visible; }
.st-key-btn_journal button{ position:absolute; top:.7rem; right:5.5rem; width:38px; height:38px; min-height:0 !important;
  padding:0 !important; border-radius:50% !important; justify-content:center; background:rgba(255,255,255,.16) !important;
  border:1px solid rgba(255,255,255,.34) !important; -webkit-backdrop-filter:blur(4px); backdrop-filter:blur(4px);
  box-shadow:none !important; color:#fff !important; }
.st-key-btn_journal button p{ display:none; }
.st-key-btn_journal ~ .st-key-btn_partage button{ top:-.1rem; }   /* compense l'espace ajouté par la pastille Journal */
/* Pastille Alertes (permis) : à gauche des autres, rouge avec compteur quand il y a des dépassements */
.st-key-btn_alertes{ position:relative; width:100% !important; height:0; z-index:30; overflow:visible; }
.st-key-btn_alertes button{ position:absolute; top:.64rem; right:5.5rem; width:38px; height:38px; min-height:0 !important;
  padding:0 !important; border-radius:50% !important; justify-content:center; background:rgba(255,255,255,.16) !important;
  border:1px solid rgba(255,255,255,.34) !important; -webkit-backdrop-filter:blur(4px); backdrop-filter:blur(4px);
  box-shadow:none !important; color:#fff !important; overflow:visible !important; }
.st-key-btn_alertes button p{ display:none; }
.st-key-btn_alertes button span{ color:#fff !important; }
.st-key-btn_alertes ~ .st-key-btn_journal button{ top:-.35rem; }
.st-key-btn_alertes ~ .st-key-btn_partage button{ top:-.35rem; }
.st-key-btn_alertes ~ .st-key-btn_journal ~ .st-key-btn_partage button{ top:-1.34rem; }
.st-key-btn_journal button span{ color:#fff !important; }
.st-key-btn_partage button span{ color:#fff !important; }
/* Bouton Partager d'une fiche : petite pastille ronde dans l'angle */
[class*="st-key-shfiche_"]{ position:relative; width:100% !important; height:0; z-index:5; overflow:visible; }
[class*="st-key-shfiche_"] button{ position:absolute; top:.05rem; right:0; width:34px; height:34px; min-height:0 !important;
  padding:0 !important; border-radius:50% !important; justify-content:center; background:rgba(201,106,63,.12) !important;
  border:1px solid rgba(201,106,63,.35) !important; color:#b5532f !important; box-shadow:none !important; }
[class*="st-key-shfiche_"] button p{ display:none; }
[class*="st-key-shfiche_"] button span{ color:#b5532f !important; }
/* Alertes permis */
.m4-banniere{ background:rgba(185,74,68,.10); border:1px solid rgba(185,74,68,.35); color:#8e2f2a; border-radius:12px;
  padding:.6rem .9rem; font-weight:600; margin:.2rem 0 .8rem; }
.m4-al{ background:var(--surface); border:1px solid var(--border); border-left:5px solid #B94A44; border-radius:14px;
  padding:.75rem .9rem; margin:.55rem 0; }
.m4-al.orange{ border-left-color:#D9A441; }
.m4-al .t{ display:flex; flex-wrap:wrap; align-items:center; gap:.4rem; margin-bottom:.35rem; }
.m4-al .l{ display:flex; align-items:baseline; gap:.5rem; font-size:.88rem; margin-top:.3rem; }
.m4-al .l span{ color:var(--muted); min-width:3.4rem; }
.m4-al .l b.r, .m4-al .l .exc{ color:#B94A44; font-weight:700; }
.m4-jauge{ height:6px; border-radius:4px; background:rgba(120,130,120,.22); overflow:hidden; margin-top:.2rem; }
.m4-jauge i{ display:block; height:100%; border-radius:4px; }
.m4-reveil{ display:flex; gap:.9rem; align-items:center; background:var(--surface); border:1px solid var(--border);
  border-radius:16px; padding:1rem 1.1rem; margin:1rem 0; }
.m4-spin{ width:26px; height:26px; border-radius:50%; border:3px solid rgba(45,106,79,.22); border-top-color:#2D6A4F;
  animation:m4tourne 1s linear infinite; flex:none; }
@keyframes m4tourne{ to{ transform:rotate(360deg); } }
.m4-reg-nom{ font-family:'Fraunces', Georgia, serif; font-size:1.1rem; font-weight:700; color:var(--accent); }

/* Barre d'actions : pictogrammes universels (Material Symbols Rounded, trait fin) dans des pastilles arrondies translucides.
   Le libellé reste dans le DOM, masqué visuellement : il sert d'aria-label aux lecteurs d'écran. */
.st-key-barre_actions [data-testid="stHorizontalBlock"]{ justify-content:flex-end !important; gap:.45rem !important; margin:0 0 .45rem; }
.st-key-barre_actions [data-testid="stColumn"], .st-key-barre_actions [data-testid="stElementContainer"]{
  flex:0 0 auto !important; width:auto !important; min-width:0 !important; }
.st-key-barre_actions [data-testid="stPopover"], .st-key-barre_actions .st-key-btn_alertes,
.st-key-barre_actions .st-key-btn_journal, .st-key-barre_actions .st-key-btn_partage{ position:static !important; width:auto !important; height:auto !important; }
.st-key-barre_actions [data-testid="stPopover"] button, .st-key-barre_actions .st-key-btn_alertes button,
.st-key-barre_actions .st-key-btn_journal button, .st-key-barre_actions .st-key-btn_partage button{
  position:relative !important; top:auto !important; right:auto !important; left:auto !important; bottom:auto !important;
  width:40px !important; height:40px !important; min-height:0 !important; padding:0 !important;
  border-radius:12px !important; display:inline-flex !important; align-items:center; justify-content:center; gap:0 !important;
  background:color-mix(in srgb, var(--accent) 11%, transparent) !important; border:1px solid color-mix(in srgb, var(--accent) 30%, transparent) !important;
  color:var(--accent) !important; box-shadow:none !important; -webkit-backdrop-filter:blur(4px); backdrop-filter:blur(4px);
  transition:background .15s, transform .15s; overflow:visible !important; }
.st-key-barre_actions [data-testid="stPopover"] button:hover, .st-key-barre_actions .st-key-btn_alertes button:hover,
.st-key-barre_actions .st-key-btn_journal button:hover, .st-key-barre_actions .st-key-btn_partage button:hover{
  background:color-mix(in srgb, var(--accent) 20%, transparent) !important; transform:translateY(-1px); }
.st-key-barre_actions [data-testid="stPopover"] button:focus-visible, .st-key-barre_actions .st-key-btn_alertes button:focus-visible,
.st-key-barre_actions .st-key-btn_journal button:focus-visible, .st-key-barre_actions .st-key-btn_partage button:focus-visible{
  outline:2px solid var(--accent) !important; outline-offset:2px; }
.st-key-barre_actions [data-testid="stPopover"] button p, .st-key-barre_actions .st-key-btn_alertes button p,
.st-key-barre_actions .st-key-btn_journal button p, .st-key-barre_actions .st-key-btn_partage button p{
  display:block !important; position:absolute !important; width:1px !important; height:1px !important; margin:-1px !important; padding:0 !important;
  overflow:hidden !important; clip:rect(0,0,0,0) !important; white-space:nowrap !important; border:0 !important; }
.st-key-barre_actions [data-testid="stPopover"] button svg, .st-key-barre_actions [data-testid="stPopover"] button > div > div:last-child{ display:none !important; }
.st-key-barre_actions button [data-testid="stIconMaterial"]{ font-size:1.3rem !important; color:var(--accent) !important;
  font-variation-settings:'FILL' 0,'wght' 300,'GRAD' 0,'opsz' 24 !important; margin:0 !important; }
</style>
"""

# Fond discret de l'application connectée (cernes d'arbre et feuillage très légers)
CSS_FOND = """
<style>
.stApp::before{ content:""; position:fixed; left:0; top:0; width:100vw; height:100vh; pointer-events:none; z-index:0;
  background:url("__FOND__") center / cover no-repeat; }
.block-container{ position:relative; z-index:1; }
</style>
"""

CSS_CONNEXION = """
<style>
.stApp{ background:#0E3426 !important; }
.stApp::before{ content:"" !important; position:fixed; inset:-5%; z-index:0; pointer-events:none; will-change:transform;
  background:url("__FEUILLAGE__") center / cover no-repeat; animation:m4-derive 48s ease-in-out infinite alternate; }
.stApp::after{ content:"" !important; position:fixed; inset:0; z-index:0; pointer-events:none;
  background:radial-gradient(circle at 50% 40%, rgba(8,36,26,.06), rgba(8,36,26,.68) 100%),
             linear-gradient(180deg, rgba(240,160,122,.07), transparent 38%); }
@keyframes m4-derive{ from{ transform:scale(1.02) translate3d(-1.2%,-.6%,0); } to{ transform:scale(1.07) translate3d(1.2%,.8%,0); } }
@media (prefers-reduced-motion:reduce){ .stApp::before{ animation:none; } .block-container, [data-testid="stForm"]{ animation:none !important; } }
.block-container{ position:relative; z-index:1; padding-top:clamp(4.5rem, 17vh, 8rem) !important;
  animation:m4-fondu .55s ease .08s both; }
@keyframes m4-fondu{ from{ opacity:0; transform:translateY(6px); } to{ opacity:1; transform:none; } }
html{ font-synthesis:none; text-rendering:optimizeLegibility; }
.m4-login{ text-align:center; margin:0 auto 1.3rem; }
.m4-emblem{ width:58px; height:58px; margin:0 auto .5rem; background:url("__EMBLEM__") no-repeat center / contain; }
.m4-wordmark{ font-family:'Fraunces', Georgia, serif; font-size:2.1rem; font-weight:700; color:#FBF6EA; letter-spacing:-.01em; line-height:1.05;
  text-shadow:0 2px 14px rgba(0,0,0,.35); }
.m4-wordmark span{ color:#F0A07A; }
.m4-trait{ width:120px; height:2px; background:#FBF6EA; opacity:.7; margin:.6rem auto .55rem; }
.m4-tag{ color:#FBF6EA; opacity:.9; font-size:.82rem; }
[data-testid="stForm"]{ max-width:380px; margin:0 auto; background:rgba(251,246,234,.14); border:1px solid rgba(251,246,234,.35) !important;
  border-radius:26px; -webkit-backdrop-filter:blur(7px); backdrop-filter:blur(7px);
  padding:1.6rem 1.35rem 1.4rem; box-shadow:0 24px 50px rgba(0,0,0,.35); }
[data-testid="stForm"] [data-testid="stTextInputRootElement"], [data-testid="stForm"] div[data-baseweb="input"], [data-testid="stForm"] div[data-baseweb="base-input"]{
  border-radius:26px !important; background:rgba(255,253,247,.94) !important; overflow:hidden; }
[data-testid="stForm"] [data-testid="stTextInputRootElement"]{ border:1.5px solid #B9AE92 !important; }
[data-testid="stForm"] div[data-baseweb="input"]{ border:0 !important; }
[data-testid="stForm"] input{ background:transparent !important; color:#1E3A2C !important; padding-left:1.1rem !important; }
[data-testid="stForm"] input::placeholder{ color:#7C7A68 !important; opacity:1; }
[data-testid="stForm"] button[kind="primaryFormSubmit"], [data-testid="stForm"] button[kind="primary"]{
  border-radius:26px !important; border:0 !important; height:3rem; text-transform:uppercase; letter-spacing:.07em; font-weight:700 !important;
  background:linear-gradient(135deg,#C8643C,#B4532E) !important; color:#fff !important; box-shadow:0 8px 18px rgba(200,100,60,.38) !important; }
[data-testid="stAlert"]{ max-width:380px; margin:.8rem auto 0; border-radius:14px; background:rgba(251,246,234,.95) !important; }
[data-testid="stAlert"] *{ color:#8E3B1F !important; }
.st-key-btn_oubli{ width:100% !important; display:flex !important; justify-content:center !important; margin-top:.4rem; }
.st-key-btn_oubli > div, .st-key-btn_oubli [data-testid="stButton"]{ width:auto !important; }
.m4-avert{ background:rgba(201,162,39,.12) !important; border-color:rgba(201,162,39,.4) !important; color:#7A5A00 !important; }
.m4-ok{ background:rgba(47,125,87,.12); border:1px solid rgba(47,125,87,.35); color:#1f6b45; border-radius:12px;
  padding:.7rem .9rem; font-size:.92rem; margin:.4rem 0; }
.st-key-btn_oubli button{ background:transparent !important; border:0 !important; box-shadow:none !important; min-height:0 !important;
  padding:.2rem .6rem !important; }
.st-key-btn_oubli button p{ color:#EADFC6 !important; text-decoration:underline; text-underline-offset:3px; font-size:.84rem; font-weight:500; }
.m4-login-foot{ text-align:center; color:#CFE3D5; opacity:.8; font-size:.74rem; margin-top:1rem; text-shadow:0 1px 6px rgba(0,0,0,.5); }
.m4-copy{ color:#CFE3D5 !important; opacity:.6 !important; }
/* --- finition : verre plus profond, icônes dans les champs, halo, bouton vivant --- */
.m4-emblem{ width:66px; height:66px; filter:drop-shadow(0 6px 18px rgba(240,160,122,.38)); }
.m4-wordmark{ font-size:2.3rem; }
.m4-trait{ width:150px; height:1.5px; opacity:.95; background:linear-gradient(90deg, transparent, #F0A07A 30%, #F0A07A 70%, transparent); }
.m4-tag{ font-size:.68rem; letter-spacing:.17em; text-transform:uppercase; opacity:.95; text-shadow:0 1px 8px rgba(5,25,18,.85); }
[data-testid="stForm"]{ max-width:400px; border-radius:30px; padding:2rem 1.55rem 1.5rem;
  background:linear-gradient(160deg, rgba(251,246,234,.22), rgba(251,246,234,.07)) !important;
  border:1px solid rgba(251,246,234,.26) !important; -webkit-backdrop-filter:blur(10px) saturate(1.15); backdrop-filter:blur(10px) saturate(1.15);
  box-shadow:0 34px 70px rgba(0,0,0,.40), 0 2px 0 rgba(255,255,255,.05), inset 0 1px 0 rgba(255,255,255,.30), inset 0 -1px 0 rgba(0,0,0,.14);
  animation:m4-monte .75s cubic-bezier(.2,.75,.2,1) .12s both; }
@keyframes m4-monte{ from{ opacity:0; transform:translateY(14px) scale(.985); } to{ opacity:1; transform:none; } }
[data-testid="stForm"] [data-testid="stTextInputRootElement"]{ background:rgba(255,253,247,.95) !important; position:relative;
  border:1.5px solid rgba(185,174,146,.9) !important; transition:border-color .18s, box-shadow .18s; }
[data-testid="stForm"] [data-testid="stTextInputRootElement"]:has(input[type="text"])::before{
  background-image:url("data:image/svg+xml;utf8,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='%23708070' stroke-width='1.7' stroke-linecap='round' stroke-linejoin='round'%3E%3Ccircle cx='12' cy='8' r='3.6'/%3E%3Cpath d='M4.5 20c.8-3.8 4-5.6 7.5-5.6s6.7 1.8 7.5 5.6'/%3E%3C/svg%3E") !important; }
[data-testid="stForm"] [data-testid="stTextInputRootElement"]:has(input[type="password"])::before{
  background-image:url("data:image/svg+xml;utf8,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='%23708070' stroke-width='1.7' stroke-linecap='round' stroke-linejoin='round'%3E%3Crect x='5' y='10.5' width='14' height='9.5' rx='2.5'/%3E%3Cpath d='M8.5 10.5V8a3.5 3.5 0 0 1 7 0v2.5'/%3E%3C/svg%3E") !important; }
[data-testid="stForm"] [data-testid="stTextInputRootElement"]::before{ content:""; position:absolute; left:.95rem; top:50%; width:1.15rem; height:1.15rem;
  margin-top:-.575rem; background:no-repeat center / contain; pointer-events:none; z-index:2; }
[data-testid="stForm"] div[data-baseweb="input"], [data-testid="stForm"] div[data-baseweb="base-input"],
[data-testid="stForm"] [data-testid="stTextInputRootElement"] > div{ background:transparent !important; }
[data-testid="stForm"] [data-testid="stTextInputRootElement"] button, [data-testid="stForm"] [data-testid="stTextInputRootElement"] button *{ color:#5B6B5E !important; background:transparent !important; }
/* remplissage automatique du navigateur (identifiants enregistrés) : même crème que le champ, texte foncé */
[data-testid="stForm"] input:-webkit-autofill, [data-testid="stForm"] input:-webkit-autofill:hover,
[data-testid="stForm"] input:-webkit-autofill:focus, [data-testid="stForm"] input:-webkit-autofill:active{
  -webkit-box-shadow:0 0 0 1000px #FDFBF4 inset !important; box-shadow:0 0 0 1000px #FDFBF4 inset !important;
  -webkit-text-fill-color:#1E3A2C !important; caret-color:#1E3A2C; transition:background-color 99999s ease-out 0s; border-radius:26px; }
/* case « Rester connecté » : boîte explicite quel que soit le thème du navigateur */
[data-testid="stForm"] [data-testid="stCheckbox"] label > div:first-of-type{ background-color:#FDFBF4 !important; border:1.5px solid #B9AE92 !important; }
[data-testid="stForm"] [data-testid="stCheckbox"] label:has(input:checked) > div:first-of-type{ background-color:#C8643C !important; border-color:#C8643C !important; }
[data-testid="stForm"] input{ padding-left:2.9rem !important; font-size:.98rem !important; }
[data-testid="stForm"] [data-testid="stTextInputRootElement"]:focus-within{ border-color:#E39A74 !important; box-shadow:0 0 0 4px rgba(240,160,122,.28) !important; }
[data-testid="stForm"] button[kind="primaryFormSubmit"], [data-testid="stForm"] button[kind="primary"]{
  height:3.1rem; transition:transform .15s, box-shadow .2s, filter .2s;
  box-shadow:inset 0 1px 0 rgba(255,255,255,.28), 0 10px 22px rgba(200,100,60,.42) !important; }
[data-testid="stForm"] button[kind="primaryFormSubmit"]:hover, [data-testid="stForm"] button[kind="primary"]:hover{
  transform:translateY(-1px); filter:brightness(1.06); box-shadow:inset 0 1px 0 rgba(255,255,255,.32), 0 14px 28px rgba(200,100,60,.52) !important; }
[data-testid="stForm"] button[kind="primaryFormSubmit"]:active{ transform:translateY(0); filter:none; }
[data-testid="stForm"] [data-testid="InputInstructions"]{ display:none !important; }
.m4-login-foot svg{ width:.85rem; height:.85rem; vertical-align:-.12rem; margin-right:.3rem; stroke:currentColor; fill:none; stroke-width:1.8; stroke-linecap:round; stroke-linejoin:round; }
@media (max-height:760px){
  .block-container{ padding-top:clamp(2.5rem, 8vh, 4rem) !important; }
  .m4-login-foot{ display:none; }
  .m4-emblem{ width:48px; height:48px; }
  .m4-wordmark{ font-size:1.8rem; }
}
</style>
"""


# ---------------------------------------------------------------------------
# Outils
# ---------------------------------------------------------------------------
def fr(valeur, decimales: int = 3) -> str:
    """12345.6 -> « 12 345,600 » (espace insécable, virgule décimale)."""
    try:
        v = float(valeur or 0)
    except (TypeError, ValueError):
        v = 0.0
    return f"{v:,.{decimales}f}".replace(",", " ").replace(".", ",")


def seg(label, options, *, key, default=None, **kw):
    """Sélecteur à segments dont un choix reste TOUJOURS actif : retoucher le choix en cours ne le désélectionne plus
    (sinon le thème, la période ou le type de rapport retombaient sur une valeur par défaut sans rien afficher)."""
    prev = f"_prev_{key}"
    if key not in st.session_state and default is not None:
        st.session_state[key] = default

    def _garder():
        if st.session_state.get(key) is None:
            st.session_state[key] = st.session_state.get(prev, default if default is not None else options[0])

    valeur = st.segmented_control(label, options, key=key, on_change=_garder, **kw)
    if valeur is None:   # premier affichage sans valeur : on active le premier choix
        valeur = st.session_state.get(prev, default if default is not None else options[0])
    st.session_state[prev] = valeur
    return valeur


def e(texte) -> str:
    return html.escape("" if texte is None else str(texte))


def cle_df10(valeur):
    """Tri naturel d'un DF10 : 54756/2/1 avant 54756/10/1."""
    cle = []
    for seg in str("" if valeur is None else valeur).strip().split("/"):
        seg = seg.strip()
        cle.append((0, int(seg), "") if seg.isdigit() else (1, 0, seg.upper()))
    return tuple(cle)


def grume_mere(df10) -> str:
    """« 53629/10/2 » -> « 53629/10 » (même règle que l'app)."""
    parts = str("" if df10 is None else df10).strip().split("/")
    return f"{parts[0].strip()}/{parts[1].strip()}" if len(parts) >= 2 else parts[0].strip()


def couleur_essence(nom: str) -> str:
    nom = (nom or "").upper()
    return COULEURS_ESSENCES.get(nom) or PALETTE_DEFAUT[zlib.crc32(nom.encode("utf-8")) % len(PALETTE_DEFAUT)]


def badge(texte: str, genre: str) -> str:
    return f'<span class="m4-badge {genre}">{e(texte)}</span>'


# Racine SQL d'un DF10 (identique à dialogs.py)
def racine_sql(col: str) -> str:
    return (f"(CASE WHEN POSITION('/' IN TRIM({col})) > 0 "
            f"THEN split_part(TRIM({col}), '/', 1) || '/' || split_part(TRIM({col}), '/', 2) "
            f"ELSE TRIM({col}) END)")


# ---------------------------------------------------------------------------
# Accès base (lecture seule)
# ---------------------------------------------------------------------------
def connecter(essais: int = 2, delai: int = 25):
    cfg = st.secrets["db"]
    derniere = None
    for _ in range(essais):  # la base en ligne peut dormir : 2e essai après réveil
        try:
            return psycopg2.connect(
                host=cfg["host"], port=int(cfg.get("port", 5432)), dbname=cfg["dbname"],
                user=cfg["user"], password=cfg["password"],
                sslmode=cfg.get("sslmode", "require"), connect_timeout=delai,
            )
        except psycopg2.OperationalError as exc:
            derniere = exc
            time.sleep(2)
    raise derniere


def reveiller_base() -> bool:
    """Neon s'endort après quelques minutes sans activité : on la réveille avec jusqu'à 6 tentatives, sous les yeux
    de l'utilisateur, au lieu d'afficher une erreur. Le résultat est mémorisé 4 minutes par session."""
    zone = st.empty()   # toujours créé, même sur le chemin rapide : garde la même structure d'éléments d'un tour à l'autre
    t = st.session_state.get("base_ok")        # (sinon l'écran de connexion s'affichait en double pendant le calcul)
    if t and time.time() - t < 240:
        return True
    derniere = None
    for n in range(1, 7):
        try:
            if n > 1:
                with zone.container():
                    st.markdown(f'<div class="m4-reveil"><div class="m4-spin"></div><div><b>Réveil de la base en ligne…</b>'
                                f'<br><small>Tentative {n} sur 6 · cela prend jusqu’à 30 secondes après une longue pause.</small></div></div>',
                                unsafe_allow_html=True)
            connecter(essais=1, delai=12).close()
            zone.empty()
            st.session_state["base_ok"] = time.time()
            return True
        except psycopg2.Error as exc:
            derniere = exc
            time.sleep(3)
    zone.empty()
    journal.warning("Base injoignable après réveil : %s", derniere)
    st.markdown('<div class="m4-vide">La base en ligne ne répond toujours pas.<br><small>Elle est probablement en train de '
                'démarrer : réessayez dans une minute.</small></div>', unsafe_allow_html=True)
    if st.button("Réessayer", type="primary", width="stretch", key="reveil_retry"):
        st.rerun()
    return False


@st.cache_resource(show_spinner=False)
def _pool() -> psycopg2.pool.ThreadedConnectionPool:
    """Connexions de lecture réutilisées d'une requête à l'autre : ouvrir une connexion TLS vers Neon coûte plusieurs
    centaines de millisecondes, et un écran en demande des dizaines. Keepalive actif pour repérer vite une connexion morte."""
    cfg = st.secrets["db"]
    return psycopg2.pool.ThreadedConnectionPool(
        1, 8, host=cfg["host"], port=int(cfg.get("port", 5432)), dbname=cfg["dbname"], user=cfg["user"], password=cfg["password"],
        sslmode=cfg.get("sslmode", "require"), connect_timeout=15,
        keepalives=1, keepalives_idle=30, keepalives_interval=10, keepalives_count=3)


def requete(sql: str, params=None) -> list[dict]:
    derniere = None
    for _ in range(3):
        pool = conn = None
        try:
            pool = _pool()
            conn = pool.getconn()
            conn.set_session(readonly=True, autocommit=True)       # lecture seule, aucune transaction laissée ouverte
            with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
                cur.execute(sql, params)
                lignes = [dict(r) for r in cur.fetchall()]
            pool.putconn(conn)
            return lignes
        except (psycopg2.OperationalError, psycopg2.InterfaceError) as exc:
            derniere = exc          # connexion périmée (base endormie, coupure réseau) : on l'écarte et on réessaie
            if pool is not None and conn is not None:
                try:
                    pool.putconn(conn, close=True)
                except Exception:
                    pass
        except psycopg2.pool.PoolError:
            break                   # pool saturé : connexion isolée ci-dessous
        except Exception:
            if pool is not None and conn is not None:      # erreur SQL (table absente, droit refusé…) : la connexion reste saine
                pool.putconn(conn)
            raise
    conn = connecter()
    try:
        conn.set_session(readonly=True)
        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(sql, params)
            return [dict(r) for r in cur.fetchall()]
    finally:
        conn.close()


@st.cache_data(ttl=TTL_DONNEES, show_spinner=False)
def q(sql: str, params=None) -> list[dict]:
    return requete(sql, params)


def ecrire(sql: str, params=None) -> bool:
    """Écriture limitée (journal des connexions, préférences) : ne doit JAMAIS bloquer l'application."""
    try:
        conn = connecter()
        try:
            with conn.cursor() as cur:
                cur.execute(sql, params)
            conn.commit()
            return True
        finally:
            conn.close()
    except Exception:
        journal.exception("Écriture impossible (tables mobile_journal / mobile_preferences créées ?)")
        return False


def appareil() -> tuple[str, str]:
    """(appareil lisible, adresse IP) d'après les en-têtes de la requête ; vide si indisponible."""
    try:
        h = st.context.headers
        ua = h.get("User-Agent", "") or ""
        ip = (h.get("X-Forwarded-For", "") or "").split(",")[0].strip()
    except Exception:
        return "", ""
    os_ = next((n for k, n in (("Android", "Android"), ("iPhone", "iPhone"), ("iPad", "iPad"), ("Windows", "Windows"),
                               ("Macintosh", "Mac"), ("Linux", "Linux")) if k in ua), "Autre")
    nav = next((n for k, n in (("Edg/", "Edge"), ("OPR/", "Opera"), ("SamsungBrowser", "Samsung Internet"),
                               ("Firefox", "Firefox"), ("Chrome", "Chrome"), ("Safari", "Safari")) if k in ua), "navigateur")
    return f"{os_} · {nav}", ip[:64]


def noter(ident: str, evenement: str, detail: str = ""):
    """Ajoute une ligne au journal des connexions (connexion, echec, blocage, deconnexion), sans faire attendre l'utilisateur."""
    appar, ip = appareil()          # lu ici : les en-têtes ne sont accessibles que depuis le fil de la session
    params = (ident[:60], evenement, detail[:120], appar, ip)

    def go():
        ecrire("INSERT INTO public.mobile_journal (identifiant, evenement, detail, appareil, ip) VALUES (%s,%s,%s,%s,%s)", params)
    # écriture en arrière-plan : l'utilisateur n'attend pas la connexion à la base pour une simple ligne de journal
    import threading
    threading.Thread(target=go, daemon=False).start()


def est_admin() -> bool:
    try:
        ids = [str(x).strip().lower() for x in st.secrets.get("admin", {}).get("ids", [])]
    except Exception:
        ids = []
    return st.session_state.get("utilisateur", {}).get("id", "").strip().lower() in ids


# ---------------------------------------------------------------------------
# Rôles : ce que chaque profil voit
# ---------------------------------------------------------------------------
TOUS_ONGLETS = ["Aperçu", "Abattage", "Carte", "Rapports", "Rechercher", "Chargement"]
DROITS = {
    "chantier":    {"onglets": ["Aperçu", "Abattage", "Carte", "Rapports", "Rechercher"], "alertes": True,  "partage": True,  "filtres": True},
    "parc":        {"onglets": ["Aperçu", "Rechercher", "Chargement"],            "alertes": False, "partage": True,  "filtres": True},
    "tracabilite": {"onglets": TOUS_ONGLETS,                                      "alertes": True,  "partage": True,  "filtres": True},
    "administration": {"onglets": ["Aperçu", "Rapports"],                         "alertes": False, "partage": True,  "filtres": True},
}
LIBELLES_ROLES = {"chantier": "Chantier", "parc": "Parc", "tracabilite": "Traçabilité", "administration": "Administration"}


def role_actuel() -> str:
    """Rôle du compte connecté. L'administrateur technique (Secrets) a tous les droits."""
    if est_admin():
        return "tracabilite"
    r = str(st.session_state.get("utilisateur", {}).get("role", "chantier")).strip().lower().replace("é", "e")
    return r if r in DROITS else "chantier"


def droits() -> dict:
    return DROITS[role_actuel()]


# ---------------------------------------------------------------------------
# Connexion des utilisateurs
# ---------------------------------------------------------------------------
@st.cache_resource
def registre_echecs() -> dict:
    return {}


@st.cache_resource
def hash_factice() -> str:
    # comparé quand l'identifiant n'existe pas : même durée de calcul, pas de fuite d'information
    return bcrypt.hashpw(b"facade", bcrypt.gensalt(rounds=12)).decode("ascii")


def verrouille(ident: str) -> int:
    """Secondes restantes de blocage pour cet identifiant (0 = libre)."""
    maintenant = time.time()
    echecs = [t for t in registre_echecs().get(ident, []) if maintenant - t < FENETRE_ECHECS]
    registre_echecs()[ident] = echecs
    if len(echecs) >= MAX_ECHECS:
        return int(FENETRE_ECHECS - (maintenant - echecs[0]))
    return 0


def tenter_connexion(identifiant: str, mot_de_passe: str):
    ident = identifiant.strip().lower()
    if not ident or not mot_de_passe:
        return None, "Saisissez l'identifiant et le mot de passe."
    reste = verrouille(ident)
    if reste:
        noter(ident, "blocage", "trop de tentatives")
        return None, f"Trop de tentatives. Réessayez dans {reste // 60 + 1} min."
    try:
        try:
            lignes = requete("SELECT identifiant, nom_affiche, mot_de_passe_hash, actif, role "
                             "FROM public.mobile_utilisateurs WHERE lower(identifiant) = %s", (ident,))
        except psycopg2.errors.UndefinedColumn:   # colonne « role » pas encore créée (commande « preparer »)
            lignes = requete("SELECT identifiant, nom_affiche, mot_de_passe_hash, actif, 'tracabilite' AS role "
                             "FROM public.mobile_utilisateurs WHERE lower(identifiant) = %s", (ident,))
    except Exception:
        journal.exception("Connexion : lecture de mobile_utilisateurs impossible")
        return None, "Service momentanément indisponible. Réessayez dans un instant."
    ligne = lignes[0] if lignes else None
    cible = ligne["mot_de_passe_hash"] if ligne else hash_factice()
    try:
        ok = bcrypt.checkpw(mot_de_passe.encode("utf-8"), cible.encode("ascii"))
    except ValueError:
        ok = False
    if ligne and ok and ligne["actif"]:
        registre_echecs().pop(ident, None)
        noter(ligne["identifiant"], "connexion")
        return {"id": ligne["identifiant"], "nom": ligne["nom_affiche"], "role": ligne.get("role") or "chantier"}, ""
    registre_echecs().setdefault(ident, []).append(time.time())
    if ligne and ok and not ligne["actif"]:
        noter(ident, "echec", "compte désactivé")
        return None, "Ce compte est bloqué. Contactez l'administrateur."
    noter(ident, "echec", "mot de passe incorrect" if ligne else "identifiant inconnu")
    return None, "Identifiant ou mot de passe incorrect."


# ---------------------------------------------------------------------------
# « Rester connecté » : jeton aléatoire (seule son empreinte est en base), cookie de 2 jours, révocable
# ---------------------------------------------------------------------------
COOKIE_SESSION = "m4_session"
VERSION_APP = "2026.11"
DUREE_SESSION_J = 2


def _empreinte(jeton: str) -> str:
    return hashlib.sha256(jeton.encode("utf-8")).hexdigest()


def _jeton_cookie() -> str:
    try:
        return (st.context.cookies.get(COOKIE_SESSION) or "").strip()
    except Exception:
        return ""


def memoriser_session(ident: str) -> str:
    """Crée le jeton de cet appareil et renvoie sa valeur ('' si la table des jetons n'existe pas encore)."""
    jeton = secrets.token_urlsafe(32)
    appar, _ = appareil()
    ok = ecrire("INSERT INTO public.mobile_jetons (empreinte, identifiant, expire_le, appareil) "
                "VALUES (%s, %s, now() + make_interval(days => %s), %s)", (_empreinte(jeton), ident[:60], DUREE_SESSION_J, appar))
    if ok:
        import threading
        threading.Thread(target=ecrire, args=("DELETE FROM public.mobile_jetons WHERE expire_le < now()",), daemon=True).start()
    return jeton if ok else ""


def oublier_session():
    """Révoque le jeton de cet appareil (déconnexion volontaire)."""
    jeton = _jeton_cookie()
    if jeton:
        ecrire("DELETE FROM public.mobile_jetons WHERE empreinte = %s", (_empreinte(jeton),))


def restaurer_session() -> bool:
    """Reconnecte l'utilisateur si son appareil porte un jeton encore valide. Sinon : écran de connexion normal."""
    jeton = _jeton_cookie()
    if not jeton or st.session_state.get("_jeton_refuse") == jeton:
        return False
    if not reveiller_base():
        st.stop()
    sql = ("SELECT u.identifiant, u.nom_affiche, u.actif, {role} AS role FROM public.mobile_jetons j "
           "JOIN public.mobile_utilisateurs u ON lower(u.identifiant) = lower(j.identifiant) "
           "WHERE j.empreinte = %s AND j.expire_le > now()")
    try:
        try:
            lignes = requete(sql.format(role="u.role"), (_empreinte(jeton),))
        except psycopg2.errors.UndefinedColumn:
            lignes = requete(sql.format(role="'tracabilite'"), (_empreinte(jeton),))
    except Exception:
        journal.info("Session mémorisée non vérifiable (table mobile_jetons créée ?)")
        return False
    if lignes and lignes[0]["actif"]:
        l = lignes[0]
        st.session_state["utilisateur"] = {"id": l["identifiant"], "nom": l["nom_affiche"], "role": l.get("role") or "chantier"}
        charger_preferences(l["identifiant"])
        noter(l["identifiant"], "connexion", "session mémorisée")
        return True
    st.session_state["_jeton_refuse"] = jeton       # expiré, révoqué ou compte bloqué : le cookie est effacé sur l'écran de connexion
    return False


JS_POSER_COOKIE = ("<script>document.cookie='" + COOKIE_SESSION + "=__J__; max-age=" + str(DUREE_SESSION_J * 86400) +
                   "; path=/; SameSite=Strict'+(location.protocol==='https:'?'; Secure':'');</script>")
JS_EFFACER_COOKIE = "<script>document.cookie='" + COOKIE_SESSION + "=; max-age=0; path=/; SameSite=Strict';</script>"


# ---------------------------------------------------------------------------
# Apparence : thème clair / sombre / auto, taille du texte (mémorisés par compte)
# ---------------------------------------------------------------------------
THEMES = ["Clair", "Soleil", "Sombre", "Auto"]
TAILLES = {"A−": 90, "A": 100, "A+": 110, "A++": 120}


def charger_preferences(ident: str):
    """Lit les préférences du compte (thème, taille) ; défauts si la table n'existe pas encore."""
    theme, taille = "Clair", "A"
    try:
        r = requete("SELECT theme, taille FROM public.mobile_preferences WHERE identifiant = %s", (ident,))
        if r:
            theme = r[0]["theme"] if r[0]["theme"] in THEMES else theme
            taille = r[0]["taille"] if r[0]["taille"] in TAILLES else taille
    except Exception:
        journal.info("Préférences non lues (table absente ?)")
    st.session_state["theme"], st.session_state["taille"] = theme, taille
    st.session_state["_prefs_ok"] = (theme, taille)


def enregistrer_preferences():
    """Mémorise un changement de thème / taille pour ce compte (si la table existe)."""
    cur = (st.session_state.get("theme") or "Clair", st.session_state.get("taille") or "A")
    if cur == st.session_state.get("_prefs_ok"):
        return
    st.session_state["_prefs_ok"] = cur
    ecrire("INSERT INTO public.mobile_preferences (identifiant, theme, taille) VALUES (%s,%s,%s) "
           "ON CONFLICT (identifiant) DO UPDATE SET theme = EXCLUDED.theme, taille = EXCLUDED.taille, modifie_le = now()",
           (st.session_state["utilisateur"]["id"], cur[0], cur[1]))


CSS_SOMBRE = """
:root{
  --bg:#0E1913; --surface:#16251D; --alt:#122019; --border:#2B4236; --text:#E8F0EA;
  --muted:#9FB8A8; --accent:#74C69D; --accent2:#52B788; --soft:#1E3228; --wood:#D9B48F; --sand:#3A2D1B;
  color-scheme:dark;
}
.stApp{ background:var(--bg) !important; color:var(--text); }
.stApp::before{ opacity:.45; }
[data-testid="stBaseButton-secondary"], .stButton>button:not([kind="primary"]){ background:var(--soft) !important; border-color:var(--border) !important; }
[data-testid="stBaseButton-secondary"] p, [data-testid="stBaseButton-secondary"] span, .stButton>button:not([kind="primary"]) p{ color:var(--text) !important; }
.m4-bille-card.exact{ background:#1B3D2D; border-color:#52B788; } .m4-bille-card.exact, .m4-bille-card.exact *{ color:var(--text); }
.stApp h1, .stApp h2, .stApp h3, .stApp h4, [data-testid="stMarkdownContainer"] p, [data-testid="stMarkdownContainer"] li,
[data-testid="stWidgetLabel"] p, [data-testid="stWidgetLabel"] label, label, [data-testid="stExpander"] summary p,
[data-testid="stSlider"] label, [data-testid="stSlider"] [data-testid="stThumbValue"],
[data-testid="stTickBarMin"], [data-testid="stTickBarMax"]{ color:var(--text) !important; }
[data-testid="stCaptionContainer"], [data-testid="stCaptionContainer"] p, small{ color:var(--muted) !important; }
div[data-baseweb="input"], div[data-baseweb="base-input"], div[data-baseweb="select"]>div, textarea, input{
  background:var(--soft) !important; color:var(--text) !important; border-color:var(--border) !important; }
input::placeholder, textarea::placeholder{ color:var(--muted) !important; opacity:1; }
div[data-baseweb="select"] svg, [data-testid="stDateInput"] svg{ fill:var(--muted) !important; }
/* Listes déroulantes et calendrier : portails hors de .stApp, thémés explicitement (plus d'inversion de couleurs) */
[data-baseweb="popover"] > div, [data-baseweb="popover"] ul, [data-baseweb="menu"], [data-baseweb="calendar"], [data-baseweb="datepicker"]{
  background:var(--surface) !important; color:var(--text) !important; border-color:var(--border) !important; }
[data-baseweb="popover"] li, [data-baseweb="popover"] [role="option"]{ background:transparent !important; color:var(--text) !important; }
[data-baseweb="popover"] li *, [data-baseweb="popover"] [role="option"] *, [data-baseweb="popover"] [role="listbox"] *, [data-baseweb="menu"] *,
[role="listbox"], [role="listbox"] *, [role="option"], [role="option"] *, [data-testid="stSelectboxVirtualDropdown"] *{
  color:var(--text) !important; -webkit-text-fill-color:var(--text) !important; }
[data-baseweb="popover"] li:hover, [data-baseweb="popover"] [role="option"][aria-selected="true"], [data-baseweb="popover"] [data-highlighted="true"]{
  background:var(--soft) !important; }
[data-testid="stMultiSelectDropdown"], [data-testid="stSelectboxVirtualDropdown"], [data-testid="stSelectboxDropdown"],
[data-testid="stMultiSelectDropdown"] > div, [data-testid="stMultiSelectDropdown"] ul{ background:var(--surface) !important; color:var(--text) !important;
  border-color:var(--border) !important; }
[data-testid="stMultiSelectDropdown"] [role="option"], [data-testid="stMultiSelectDropdown"] li, [data-testid="stMultiSelectDropdown"] span,
[data-testid="stMultiSelectDropdown"] div{ color:var(--text) !important; }
[data-testid="stMultiSelectDropdown"] [role="option"]:hover, [data-testid="stMultiSelectDropdown"] [aria-selected="true"]{ background:var(--soft) !important; }
[data-testid="stDateInputCalendar"]{ background:var(--surface) !important; color:var(--text) !important; border:1px solid var(--border); border-radius:12px; }
[data-testid="stDateInputCalendar"] *{ color:var(--text) !important; background-color:transparent !important; }
[data-testid="stDateInputCalendar"] svg{ fill:var(--text) !important; }
[data-testid="stDateInputCalendar"] [aria-selected="true"], [data-testid="stDateInputCalendar"] [aria-selected="true"] *{
  background-color:var(--accent2) !important; color:#06130C !important; border-radius:8px; }
[data-baseweb="calendar"] *{ color:var(--text) !important; background-color:transparent !important; }
[data-baseweb="calendar"] [aria-label*="Selected"], [data-baseweb="calendar"] [aria-selected="true"]{ background-color:var(--accent2) !important; color:#06130C !important; }
[data-baseweb="calendar"] [aria-disabled="true"]{ opacity:.35; }
[data-baseweb="calendar"] svg{ fill:var(--text) !important; }
[data-testid="stTooltipIcon"] svg, [data-testid="stTooltipIcon"] svg *{ color:#B7CDBF !important; stroke:#B7CDBF !important; opacity:1 !important; }
/* Bulles d'aide (?) : fond sombre et texte clair, lisibles quel que soit le thème Streamlit sous-jacent */
[data-testid="stTooltipContent"]{ background:var(--soft) !important; color:var(--text) !important; border:1px solid var(--border) !important;
  border-radius:10px !important; box-shadow:0 6px 18px rgba(0,0,0,.45) !important; }
[data-testid="stTooltipContent"] *{ background:transparent !important; color:var(--text) !important; -webkit-text-fill-color:var(--text) !important; }
[data-testid="stTooltipContent"] a{ color:var(--accent) !important; -webkit-text-fill-color:var(--accent) !important; }
textarea:focus, div[data-baseweb="textarea"]:focus-within{ border-color:var(--accent) !important; outline:none !important; box-shadow:0 0 0 1px var(--accent) !important; }
[data-testid="stPopoverBody"]{ background:var(--surface) !important; border:1px solid var(--border) !important; color:var(--text); }
.stButton>button, .stDownloadButton>button{ background:var(--surface); color:var(--text); border-color:var(--border); }
.stButton>button p, .stDownloadButton>button p{ color:var(--text) !important; }
.stButton>button[kind="primary"] p, button[data-testid="stBaseButton-primary"] p{ color:#fff !important; }
div[data-testid="stDataFrame"]{ filter:invert(.92) hue-rotate(180deg); border-color:var(--border); }
div[data-testid="stVerticalBlockBorderWrapper"]{ border-color:var(--border); }
.m4-card[open] > summary{ background:linear-gradient(var(--alt),var(--surface)); }
.m4-kpi, .m4-card, .m4-sub, .m4-mx-wrap, [data-testid="stExpander"]{ box-shadow:none; }
.m4-mx th, .m4-mx td{ border-bottom-color:var(--border); }
.m4-pl.on .m4-pl-t{ background:#35503F; }
.m4-c.bad, .m4-badge.bad{ background:#3A1F1E; color:#F3B8B2; border-color:#603230; }
.m4-avert{ color:#E6C86A !important; }
.m4-ok{ background:rgba(95,190,140,.14); border-color:rgba(95,190,140,.4); color:#A8E3C4; }
.m4-banniere{ background:rgba(240,138,131,.14); border-color:rgba(240,138,131,.45); color:#F6B9B3; }
.m4-al .l b.r, .m4-al .l .exc{ color:#F08A83; }
.m4-jauge{ background:rgba(255,255,255,.14); }
.m4-reveil{ background:var(--surface); border-color:var(--border); color:var(--text); }
/* Fenêtres (Partager, Journal) : portail hors de .stApp, à thémer explicitement */
[data-testid="stDialog"] > div, [data-testid="stDialog"] section[role="dialog"]{ background:var(--surface) !important; color:var(--text) !important;
  border:1px solid var(--border); }
[data-testid="stDialog"] h1, [data-testid="stDialog"] h2, [data-testid="stDialog"] h3, [data-testid="stDialog"] label,
[data-testid="stDialog"] [data-testid="stWidgetLabel"] p, [data-testid="stDialog"] [data-testid="stMarkdownContainer"] p,
[data-testid="stDialog"] [data-testid="stCaptionContainer"] p, [data-testid="stDialog"] button[aria-label="Close"]{ color:var(--text) !important; }
[data-testid="stDialog"] [data-testid="stCaptionContainer"] p{ color:var(--muted) !important; }
[data-testid="stDialog"] .stDownloadButton>button{ background:var(--soft); color:var(--text); }
[data-testid="stDialog"] .m4-al, [data-testid="stDialog"] .m4-al b{ color:var(--text); }
.m4-c.warn, .m4-badge.warn{ background:#3A2D12; color:#EDC77F; border-color:#5E4A1F; }
.m4-c.ok, .m4-badge.ok{ background:#17382A; color:#8FD8AE; border-color:#2A5A42; }
.m4-c.wood{ background:#38291A; color:#E0BC98; border-color:#5A4329; }
.m4-badge.neutral{ background:#1F2F26; color:#AFC5B7; border-color:#34493D; }
.m4-total .m4-c{ background:rgba(255,255,255,.14); color:#fff; border-color:rgba(255,255,255,.26); }
.m4-copy.clair{ color:#8FB09B; }
div[data-testid="stExpander"], div[data-testid="stExpander"] details, div[data-testid="stExpander"] summary{
  background:var(--surface) !important; color:var(--text) !important; border-color:var(--border) !important; }
div[data-testid="stExpander"] summary:hover{ background:var(--alt) !important; }
div[data-baseweb="select"]{ background:var(--soft) !important; border-radius:12px !important; }
div[data-baseweb="select"] > div, div[data-baseweb="select"] div[class*="Container"]{ background:transparent !important; border-color:var(--border) !important; }
[data-testid="stSelectbox"] [data-baseweb="select"] div, [data-testid="stSelectbox"] [data-baseweb="select"] span,
[data-testid="stSelectbox"] [data-baseweb="select"] input{ color:var(--text) !important; -webkit-text-fill-color:var(--text) !important; }
[data-testid="stSelectbox"] [data-baseweb="select"] input::placeholder{ color:var(--muted) !important; -webkit-text-fill-color:var(--muted) !important; opacity:1; }
[data-testid="stTextInputRootElement"], [data-testid="stDateInputField"], [data-testid="stNumberInputContainer"]{
  background:var(--soft) !important; border-color:var(--border) !important; }
div[data-baseweb="input"]:focus-within, div[data-baseweb="base-input"]:focus-within{ border-color:var(--accent) !important; }
[data-testid="stSelectbox"] div:has(> input), [data-testid="stMultiSelect"] div:has(input), [data-testid="stDateInput"] div:has(> input){ border-radius:12px;
  background:var(--soft) !important; border-color:var(--border) !important; }
[data-testid="stDateInput"] input::placeholder{ color:var(--muted) !important; opacity:1 !important; }
[data-testid="stTooltipIcon"] svg, [data-testid="stTooltipHoverTarget"] svg{ color:var(--muted) !important; }
[data-testid="stMultiSelect"] [data-baseweb="tag"]{ background:#2A4A38 !important; color:var(--text) !important; }
[data-testid="stSelectbox"] div:has(> input) > *, [data-testid="stMultiSelect"] div:has(input) > div:not(:has(span)){ background:transparent !important; }
/* Champs de date (jj / mm / aaaa) : le thème de Streamlit reste clair, donc le texte restait sombre sur fond sombre */
[data-testid="stDateInputField"], [data-testid="stDateInputField"] [role="spinbutton"], [data-testid="stDateInputField"] [data-type="day"],
[data-testid="stDateInputField"] [data-type="month"], [data-testid="stDateInputField"] [data-type="year"]{ color:var(--text) !important; }
[data-testid="stDateInputField"] [data-type="literal"]{ color:var(--muted) !important; opacity:1 !important; }
[data-testid="stDateInputField"] [role="spinbutton"]:focus{ background:var(--accent2) !important; color:#06130C !important; border-radius:6px; outline:none; }
[data-testid="stDateInputCalendarButton"] svg{ fill:var(--muted) !important; }
[data-testid="stDateInputCalendarButton"]:hover svg{ fill:var(--text) !important; }
/* petits blocs de code (identifiants, séquences) : fond clair illisible dans le thème sombre */
[data-testid="stMarkdownContainer"] code{ background:var(--soft) !important; color:#8FD8AE !important; border:1px solid var(--border); }
.m4-brand small{ color:#C9ECD6 !important; }
[data-testid="stButtonGroup"] button[aria-checked="true"] p, [data-testid="stButtonGroup"] button[aria-checked="true"] span{ color:#fff !important; }
[data-testid="stSliderThumbValue"], [data-testid="stSliderThumbValue"] p{ color:#fff !important; }
"""


CSS_SOLEIL = """
:root{
  --bg:#FFFFFF; --surface:#FFFFFF; --alt:#F8FAFC; --border:#64748B; --text:#000000;
  --muted:#1E293B; --accent:#14532D; --accent2:#15803D; --soft:#E2E8F0; --deep:#052E16;
  --wood:#5C2D16; --sand:#FEF3C7; --danger:#991B1B; --warn:#92400E;
}
.stApp{ background:#FFFFFF !important; color:#000000 !important; }
.stApp::before{ display:none !important; }
.m4-kpi, .m4-card, .m4-sub, .m4-mx-wrap, [data-testid="stExpander"]{ border:2px solid #475569 !important; box-shadow:none !important; }
.m4-hero{ background:#052E16 !important; border:2px solid #000 !important; }
.m4-total{ background:#052E16 !important; border:2px solid #000 !important; }
"""

def url_fond() -> str:
    """Fond de l'application : fichier statique mis en cache par le navigateur (static/fond_clair.svg, avec
    enableStaticServing dans .streamlit/config.toml) ; à défaut, image intégrée au style comme auparavant."""
    try:
        if st.get_option("server.enableStaticServing") and os.path.exists(os.path.join(os.path.dirname(os.path.abspath(__file__)), "static", "fond_clair.svg")):
            base = (st.get_option("server.baseUrlPath") or "").strip("/")
            return (f"/{base}" if base else "") + "/app/static/fond_clair.svg"
    except Exception:
        pass
    return arts()["fond"]


def css_apparence() -> str:
    """CSS du thème et de la taille du texte choisis par la personne connectée."""
    theme = st.session_state.get("theme") or "Clair"
    taille = TAILLES.get(st.session_state.get("taille") or "A", 100)
    out = ""
    if taille != 100:
        out += f"html{{ font-size:{taille}% !important; }}"
    if theme == "Soleil":
        out += CSS_SOLEIL
    elif theme == "Sombre":
        out += CSS_SOMBRE
    elif theme == "Auto":
        out += "@media (prefers-color-scheme: dark){" + CSS_SOMBRE + "}"
    return f"<style>{out}</style>" if out else ""



# ---------------------------------------------------------------------------
# Mot de passe oublié : demande transmise à l'administrateur (+ contact direct WhatsApp / e-mail)
# ---------------------------------------------------------------------------
MAX_DEMANDES_SESSION = 3


def contact_admin() -> dict:
    """Coordonnées de l'administrateur : Secrets → [contact] whatsapp = "2376…", email = "…", nom = "…"."""
    try:
        c = dict(st.secrets.get("contact", {}))
    except Exception:
        c = {}
    c["whatsapp"] = re.sub(r"\D", "", str(c.get("whatsapp", "") or ""))
    return c


def enregistrer_demande(ident: str, joindre: str, message: str) -> bool:
    appar, ip = appareil()
    return ecrire("INSERT INTO public.mobile_demandes (identifiant, contact, message, appareil, ip) VALUES (%s,%s,%s,%s,%s)",
                  (ident[:60], joindre[:60], message[:300], appar, ip))


@st.dialog("Mot de passe oublié", width="small")
def dialogue_oubli():
    st.markdown("Indiquez votre identifiant : l'administrateur recevra votre demande et vous transmettra un "
                "**nouveau mot de passe provisoire** par un canal privé.")
    ident = st.text_input("Votre identifiant", key="oubli_ident", placeholder="Identifiant", max_chars=60)
    joindre = st.text_input("Comment vous joindre (téléphone / WhatsApp)", key="oubli_contact", max_chars=60,
                            placeholder="Ex. 6 90 00 00 00")
    message = st.text_area("Message (facultatif)", key="oubli_msg", max_chars=300, height=70,
                           placeholder="Ex. Je ne retrouve plus mon mot de passe.")
    if st.button("Envoyer la demande", type="primary", width="stretch", key="oubli_envoi", icon=":material/send:"):
        if not ident.strip():
            st.warning("Saisissez votre identifiant.")
        elif st.session_state.get("nb_demandes", 0) >= MAX_DEMANDES_SESSION:
            st.warning("Trop de demandes depuis cet appareil. Contactez directement l'administrateur.")
        else:
            st.session_state["nb_demandes"] = st.session_state.get("nb_demandes", 0) + 1
            deja = False
            try:   # une seule demande en attente par identifiant (évite les doublons et le spam)
                deja = bool(requete("SELECT 1 FROM public.mobile_demandes WHERE identifiant = %s AND NOT traitee "
                                    "AND quand > now() - interval '30 minutes'", (ident.strip().lower(),)))
            except Exception:
                pass
            if deja or enregistrer_demande(ident.strip().lower(), joindre.strip(), message.strip()):
                # même réponse que le compte existe ou non : on ne révèle jamais quels identifiants existent
                st.markdown('<div class="m4-ok">✔ Demande transmise. L’administrateur vous répondra dès que possible.</div>',
                            unsafe_allow_html=True)
            else:
                st.error("Envoi impossible pour le moment. Utilisez le contact direct ci-dessous.")
    c = contact_admin()
    if c.get("whatsapp") or c.get("email"):
        st.markdown('<div class="m4-sec" style="margin-top:.8rem">Ou contactez directement'
                    + (f" {e(c['nom'])}" if c.get("nom") else " l’administrateur") + '</div>', unsafe_allow_html=True)
        from urllib.parse import quote
        texte = f"Bonjour, j'ai oublié mon mot de passe Mich4Track. Mon identifiant : {ident.strip() or '…'}"
        if c.get("whatsapp"):
            st.link_button("Écrire sur WhatsApp", f"https://wa.me/{c['whatsapp']}?text={quote(texte)}", width="stretch",
                           icon=":material/chat:")
        if c.get("email"):
            st.link_button("Envoyer un e-mail", f"mailto:{c['email']}?subject={quote('Mich4Track : mot de passe oublié')}"
                           f"&body={quote(texte)}", width="stretch", icon=":material/mail:")


def demandes_en_attente() -> list[dict]:
    try:
        return requete("SELECT id, quand, identifiant, contact, message FROM public.mobile_demandes WHERE NOT traitee "
                 "ORDER BY quand DESC LIMIT 100")
    except Exception:
        return []


def vue_demandes():
    """Demandes de mot de passe en attente (administrateurs) : à traiter sur le PC avec « reinitialiser »."""
    lignes = demandes_en_attente()
    if not lignes:
        st.markdown('<div class="m4-vide">Aucune demande en attente.</div>', unsafe_allow_html=True)
        return
    st.caption("Sur le PC : python gerer_utilisateurs_mobile.py reinitialiser <identifiant> — puis transmettez le "
               "mot de passe provisoire par un canal privé. La demande est alors classée automatiquement.")
    for r in lignes:
        quand = pd.to_datetime(r["quand"], utc=True).tz_convert("Africa/Douala")
        with st.container(border=True):
            st.markdown(f'**{e(r["identifiant"])}**  \n'
                        f'{quand:%d/%m/%Y à %H:%M}{" · " + e(r["contact"]) if r["contact"] else ""}'
                        + (f'  \n_{e(r["message"])}_' if r["message"] else ""))
            if st.button("Marquer comme traitée", key=f"dem_{r['id']}", icon=":material/check:"):
                if ecrire("UPDATE public.mobile_demandes SET traitee = true, traitee_le = now() WHERE id = %s", (int(r["id"]),)):
                    st.cache_data.clear()
                    st.rerun(scope="fragment")


@st.cache_resource(ttl=240, show_spinner=False)
def _chauffer_base() -> bool:
    """Réveille la base en ligne en arrière-plan pendant que l'utilisateur saisit ses identifiants."""
    import threading

    def go():
        try:
            connecter(essais=3, delai=12).close()
        except Exception:
            return
        _prechauffer_donnees()
    threading.Thread(target=go, daemon=True).start()
    return True


def _prechauffer_donnees():
    """Remplit le cache avec les chiffres du premier écran (sans filtre), en parallèle, pendant la saisie des identifiants.
    Rien n'est envoyé au navigateur : la connexion trouvera ensuite tout prêt. Une erreur ici est sans conséquence."""
    from concurrent.futures import ThreadPoolExecutor
    taches = [charger_donnees, charger_evac, listes_filtres, derniere_synchro, liste_sites,
              charger_bilan_sites, charger_pieds_autorises, lambda: charger_alertes([], [])]

    def lancer(f):
        try:
            f()
        except Exception:
            journal.info("Préchargement ignoré : %s", getattr(f, "__name__", "tâche"))
    with ThreadPoolExecutor(max_workers=4) as ex:
        list(ex.map(lancer, taches))


# Écran de connexion : curseur dans « Identifiant » (ordinateur seulement : sur téléphone le clavier masquerait l'écran),
# bouton « Connexion… » dès le toucher, curseur ramené sur le mot de passe après une erreur.
JS_CONNEXION = """<style>
[data-testid="stForm"] [data-testid="stCheckbox"]{ margin:.1rem 0 .15rem; }
[data-testid="stForm"] [data-testid="stCheckbox"] p{ color:rgba(243,239,227,.92) !important; font-size:.84rem !important; }
[data-testid="stForm"] [data-testid="stCheckbox"] svg, [data-testid="stForm"] [data-testid="stTooltipIcon"] svg{ color:rgba(243,239,227,.85) !important; }
[data-testid="stForm"] [data-testid="stCheckbox"] label > span:first-of-type:not(:has(svg)){ border-color:rgba(243,239,227,.7) !important; background:rgba(255,255,255,.08) !important; }
button[data-m4-busy]{ pointer-events:none; position:relative; }
button[data-m4-busy] p{ visibility:hidden; }
button[data-m4-busy]::after{ content:"Connexion…"; position:absolute; inset:0; display:flex; align-items:center; justify-content:center;
  font-weight:600; }
button[data-m4-busy]::before{ content:""; position:absolute; left:calc(50% - 6.3rem); top:calc(50% - .5rem); width:1rem; height:1rem;
  border:2px solid currentColor; border-right-color:transparent; border-radius:50%; animation:m4tourne .7s linear infinite; }
</style>
<script>
(function(){
  if(window.__m4Connexion){ window.__m4Connexion.focus(); return; }
  const doc = document;
  const fin = matchMedia("(pointer:fine)").matches;
  function formulaire(){ const f = doc.querySelector('[data-testid="stForm"]'); return f && f.querySelector('input[type="password"]') ? f : null; }
  function bouton(){ const f = formulaire(); return f ? f.querySelector('button[kind="primaryFormSubmit"], button[data-testid^="stBaseButton-primary"]') : null; }
  function occupe(){ const b = bouton(); if(b){ b.setAttribute("data-m4-busy","1"); setTimeout(libere, 25000); } }
  function libere(){ const b = bouton(); if(b) b.removeAttribute("data-m4-busy"); }
  function focus(){
    if(!fin) return;
    const f = formulaire(); if(!f) return;
    const i = f.querySelector('input[type="text"]'); if(i && !i.value) i.focus({preventScroll:true});
  }
  doc.addEventListener("click", e => { const b = e.target.closest && e.target.closest("button"); if(b && b === bouton()) occupe(); }, true);
  doc.addEventListener("keydown", e => { if(e.key === "Enter" && e.target && e.target.type === "password" && formulaire() && formulaire().contains(e.target)) occupe(); }, true);
  let nbAlertes = 0;
  new MutationObserver(() => {
    const n = doc.querySelectorAll('[data-testid="stAlert"]').length;
    if(n !== nbAlertes){ nbAlertes = n; libere(); if(n && fin){ const p = formulaire() && formulaire().querySelector('input[type="password"]'); if(p) p.focus({preventScroll:true}); } }
  }).observe(doc.body, {childList:true, subtree:true});
  window.__m4Connexion = {focus};
  focus(); setTimeout(focus, 300);
})();
</script>"""


def ecran_connexion():
    a = arts()
    # un SEUL bloc de style, envoyé en premier : le fond sombre s'affiche d'emblée (pas de page claire puis sombre)
    st.html(CSS.replace("__ENTETE__", a["entete"])
            + CSS_CONNEXION.replace("__FEUILLAGE__", a["feuillage"]).replace("__EMBLEM__", a["emblem_ivoire"]))
    _chauffer_base()
    st.html(JS_CONNEXION, unsafe_allow_javascript=True)
    if st.session_state.get("_jeton_refuse"):
        st.html(JS_EFFACER_COOKIE, unsafe_allow_javascript=True)
    with st.form("connexion", clear_on_submit=False):
        st.markdown('<div class="m4-login"><div class="m4-emblem"></div>'
                    '<div class="m4-wordmark">Mich4<span>Track</span></div><div class="m4-trait"></div>'
                    '<div class="m4-tag">Suivi forestier · consultation sécurisée</div></div>', unsafe_allow_html=True)
        ident = st.text_input("Identifiant", autocomplete="username", placeholder="Identifiant", label_visibility="collapsed")
        mdp = st.text_input("Mot de passe", type="password", autocomplete="current-password",
                            placeholder="Mot de passe", label_visibility="collapsed")
        rester = st.checkbox(f"Rester connecté {DUREE_SESSION_J} jours sur cet appareil", key="rester",
                             help="À cocher seulement sur votre téléphone personnel. La déconnexion (Réglages) efface cette mémoire.")
        envoi = st.form_submit_button("Se connecter", type="primary", width="stretch")
    if envoi:
        if not reveiller_base():
            return
        utilisateur, message = tenter_connexion(ident, mdp)
        if utilisateur:
            st.session_state["utilisateur"] = utilisateur
            charger_preferences(utilisateur["id"])      # le thème est connu dès le premier affichage de l'application
            if rester:
                st.session_state["_poser_cookie"] = memoriser_session(utilisateur["id"])
            st.rerun()
        st.error(message)
    if st.button("Mot de passe oublié ?", type="tertiary", key="btn_oubli"):
        dialogue_oubli()
    st.markdown('<div class="m4-login-foot"><svg viewBox="0 0 24 24" width="14" height="14"><rect x="5" y="10.5" width="14" height="9.5" rx="2.5"/>'
                '<path d="M8.5 10.5V8a3.5 3.5 0 0 1 7 0v2.5"/></svg>Connexion chiffrée · accès réservé aux membres autorisés · lecture seule</div>'
                f'<div class="m4-copy">© Ngapout Mbarga Michel Mohamed 2026 · v{VERSION_APP}</div>',
                unsafe_allow_html=True)


# ---------------------------------------------------------------------------
# Requêtes métier
# ---------------------------------------------------------------------------
def derniere_synchro():
    try:
        lignes = q("SELECT locale FROM public.synchro_info WHERE id = 1")
        if lignes:
            return datetime.strptime(lignes[0]["locale"], "%d/%m/%Y %H:%M")
    except Exception:
        pass
    return None


def listes_filtres():
    titres = q("SELECT DISTINCT TRIM(titre) AS v FROM abattage WHERE TRIM(COALESCE(titre,'')) <> '' "
               "UNION SELECT DISTINCT TRIM(titre) FROM billonnage WHERE TRIM(COALESCE(titre,'')) <> '' ORDER BY 1")
    essences = q("SELECT DISTINCT UPPER(TRIM(essence)) AS v FROM abattage WHERE TRIM(COALESCE(essence,'')) <> '' "
                 "UNION SELECT DISTINCT UPPER(TRIM(essence)) FROM billonnage WHERE TRIM(COALESCE(essence,'')) <> '' ORDER BY 1")
    return [t["v"] for t in titres], [x["v"] for x in essences]


SQL_PERTE = f"""
WITH f AS (
  SELECT {racine_sql('b.df10')} AS grume, COALESCE(SUM(b.volume),0) AS v_filles,
         MAX(UPPER(TRIM(b.essence))) AS ess_f, MAX(TRIM(b.titre)) AS titre_f
  FROM billonnage b WHERE TRIM(COALESCE(b.df10,'')) <> '' GROUP BY 1),
a AS (
  SELECT {racine_sql('a.df10')} AS grume, COALESCE(SUM(a.volume),0) AS v_mere,
         MAX(UPPER(TRIM(a.essence))) AS ess_a, MAX(TRIM(a.titre)) AS titre_a
  FROM abattage a WHERE TRIM(COALESCE(a.df10,'')) <> '' GROUP BY 1)
SELECT COALESCE(a.ess_a, f.ess_f, '') AS essence, COALESCE(a.titre_a, f.titre_f, '') AS titre,
       COUNT(*) AS n, COALESCE(SUM(a.v_mere),0) AS v_mere, COALESCE(SUM(f.v_filles),0) AS v_filles
FROM f LEFT JOIN a ON a.grume = f.grume GROUP BY 1, 2
"""

CHAMPS = ("abattu", "n_abattu", "billonne", "n_billes", "abandon", "evacue", "usine", "n_usine",
          "perte_base", "perte_filles", "n_grumes_b")


def charger_donnees() -> pd.DataFrame:
    """Une ligne par (essence, titre) avec toutes les étapes. Tous les rapports en dérivent."""
    abattu = q("SELECT COALESCE(UPPER(TRIM(essence)),'') AS essence, COALESCE(TRIM(titre),'') AS titre, "
               "COALESCE(SUM(volume),0) AS v, COUNT(*) AS n FROM abattage GROUP BY 1, 2")
    billon = q("SELECT COALESCE(UPPER(TRIM(essence)),'') AS essence, COALESCE(TRIM(titre),'') AS titre, "
               "COALESCE(SUM(volume) FILTER (WHERE UPPER(TRIM(COALESCE(statut,''))) <> 'ABANDON'),0) AS v, COUNT(*) FILTER (WHERE UPPER(TRIM(COALESCE(statut,''))) <> 'ABANDON') AS n, "
               "COALESCE(SUM(volume) FILTER (WHERE UPPER(TRIM(COALESCE(statut,''))) = 'ABANDON'),0) AS aban, "
               "COALESCE(SUM(volume) FILTER (WHERE UPPER(TRIM(COALESCE(situation,''))) = ANY(%s) "
               "AND UPPER(TRIM(COALESCE(statut,''))) <> 'ABANDON'),0) AS evac "
               "FROM billonnage GROUP BY 1, 2", [SITUATIONS_EVACUEES])
    usine = q("SELECT COALESCE(UPPER(TRIM(essence)),'') AS essence, COALESCE(TRIM(titre),'') AS titre, "
              "COALESCE(SUM(volume),0) AS v, COUNT(*) AS n FROM billonnage "
              "WHERE UPPER(TRIM(COALESCE(situation,''))) = 'PARC USINE' AND UPPER(TRIM(COALESCE(statut,''))) <> 'ABANDON' GROUP BY 1, 2")
    perte = q(SQL_PERTE)
    res: dict[tuple, dict] = {}

    def ligne(r):
        return res.setdefault((r["essence"], r["titre"]), dict.fromkeys(CHAMPS, 0.0))

    for r in abattu:
        d = ligne(r)
        d["abattu"], d["n_abattu"] = float(r["v"]), r["n"]
    for r in billon:
        d = ligne(r)
        d["billonne"], d["n_billes"] = float(r["v"]), r["n"]
        d["abandon"], d["evacue"] = float(r["aban"]), float(r["evac"])
    for r in usine:
        d = ligne(r)
        d["usine"], d["n_usine"] = float(r["v"]), r["n"]
    for r in perte:
        d = ligne(r)
        d["perte_base"], d["perte_filles"], d["n_grumes_b"] = float(r["v_mere"]), float(r["v_filles"]), r["n"]
    df = pd.DataFrame([{"essence": k[0], "titre": k[1], **v} for k, v in res.items()])
    if df.empty:
        return pd.DataFrame(columns=["essence", "titre", *CHAMPS])
    return df


# Date d'évacuation lue de façon tolérante (colonne date OU texte « 2026-10-17 » / « 17/10/2026 »)
DATE_EVAC = ("(CASE WHEN b.date_evacuation::text ~ '^\\d{4}-\\d{2}-\\d{2}' "
             "THEN substr(b.date_evacuation::text, 1, 10)::date "
             "WHEN b.date_evacuation::text ~ '^\\d{2}/\\d{2}/\\d{4}' "
             "THEN to_date(substr(b.date_evacuation::text, 1, 10), 'DD/MM/YYYY') END)")
SIT_EVAC = "UPPER(TRIM(COALESCE(b.situation,''))) = ANY(%s)"
NON_ABANDON = "UPPER(TRIM(COALESCE(b.statut,''))) <> 'ABANDON'"
CLE_LV = "COALESCE(NULLIF(TRIM(b.numero_lv),''), NULLIF(TRIM(b.code_barre_lv),''))"
COLS_EVAC = ["essence", "titre", "date", "lv", "camion", "volume"]


def charger_evac() -> pd.DataFrame:
    """Une ligne par bille évacuée (hors Abandon) : essence, titre, date, N° LV, camion, volume."""
    lignes = q(f"SELECT COALESCE(UPPER(TRIM(b.essence)),'') AS essence, COALESCE(TRIM(b.titre),'') AS titre, "
               f"{DATE_EVAC} AS date, {CLE_LV} AS lv, NULLIF(TRIM(b.camion),'') AS camion, "
               f"COALESCE(b.volume,0) AS volume FROM billonnage b WHERE {SIT_EVAC} AND {NON_ABANDON}",
               [SITUATIONS_EVACUEES])
    df = pd.DataFrame(lignes, columns=COLS_EVAC)
    if not df.empty:
        df["volume"] = df["volume"].astype(float)
        df["date"] = pd.to_datetime(df["date"])
    return df


def stats_evac(ev: pd.DataFrame) -> dict:
    """Volume, nombre de billes, de LV distincts et de camions distincts d'un ensemble d'évacuations."""
    return {"volume": float(ev["volume"].sum()), "billes": int(len(ev)), "lv": int(ev["lv"].nunique()),
            "camions": int(ev["camion"].nunique()), "sans_lv": int(ev["lv"].isna().sum()),
            "du": ev["date"].min() if len(ev) else pd.NaT, "au": ev["date"].max() if len(ev) else pd.NaT}


def cle_naturelle(texte) -> tuple:
    """Tri naturel : LV2 avant LV10."""
    return tuple((0, int(p), "") if p.isdigit() else (1, 0, p.upper())
                 for p in re.split(r"(\d+)", str(texte)) if p != "")


FUSEAU = timezone(timedelta(hours=1))   # Douala (UTC+1)
PERIODES = ["Tout", "7 jours", "30 jours", "Ce mois", "Choisir"]


def choix_periode(cle: str, etiquette: str = "Période") -> tuple:
    """Sélecteur de période (raccourcis + dates libres). Retourne (du, au) ; None = pas de borne."""
    p = seg(etiquette, PERIODES, default="Tout", key=f"per_{cle}", label_visibility="collapsed") or "Tout"
    auj = datetime.now(FUSEAU).date()
    if p == "7 jours":
        return auj - timedelta(days=6), auj
    if p == "30 jours":
        return auj - timedelta(days=29), auj
    if p == "Ce mois":
        return auj.replace(day=1), auj
    if p == "Choisir":
        c1, c2 = st.columns(2)
        du = c1.date_input("Du", value=None, format="DD/MM/YYYY", key=f"du_{cle}")
        au = c2.date_input("Au", value=None, format="DD/MM/YYYY", key=f"au_{cle}")
        return du, au
    return None, None


def texte_periode(du, au) -> str:
    if du and au:
        return f"du {du:%d/%m/%Y} au {au:%d/%m/%Y}"
    if du:
        return f"depuis le {du:%d/%m/%Y}"
    if au:
        return f"jusqu'au {au:%d/%m/%Y}"
    return "toute la période"


def filtrer(df: pd.DataFrame, titre: list, essence: list) -> pd.DataFrame:
    """Filtres du haut de page (listes : aucun choix = tout)."""
    if titre:
        df = df[df["titre"].isin(titre)]
    if essence:
        df = df[df["essence"].isin(essence)]
    return df


def filtres_globaux() -> tuple[list, list]:
    return list(st.session_state.get("ft") or []), list(st.session_state.get("fe") or [])


def nb_df10(titre: list, essence: list) -> int:
    """Nombre de DF10 (carnets) utilisés à l'abattage : premier segment du numéro, distincts."""
    w, p = ["TRIM(COALESCE(a.df10,'')) <> ''"], []
    if titre:
        w.append("TRIM(a.titre) = ANY(%s)")
        p.append(list(titre))
    if essence:
        w.append("UPPER(TRIM(a.essence)) = ANY(%s)")
        p.append(list(essence))
    r = q("SELECT COUNT(DISTINCT split_part(TRIM(a.df10), '/', 1)) AS n FROM abattage a WHERE " + " AND ".join(w), p)
    return int(r[0]["n"]) if r else 0


def totaux(df: pd.DataFrame) -> dict:
    """Somme + indicateurs dérivés (perte, taux d'évacuation)."""
    t = {c: float(df[c].sum()) if len(df) else 0.0 for c in CHAMPS}
    t["perte"] = t["perte_base"] - t["perte_filles"]
    t["perte_pct"] = (t["perte"] / t["perte_base"] * 100) if t["perte_base"] > 0 else 0.0
    exploite = t["billonne"]   # « Exploité » = billonné hors Abandon
    t["taux_evac"] = (t["evacue"] / exploite * 100) if exploite > 0 else 0.0
    return t


def agreger(df: pd.DataFrame, par: str) -> list[tuple[str, dict]]:
    out = []
    for cle, sous in df.groupby(par, sort=False):
        t = totaux(sous)
        if any(abs(t[c]) > 0.0005 for c in ("abattu", "billonne", "abandon", "evacue", "usine", "perte_base", "perte_filles")):
            out.append((cle, t))   # une essence / un titre à 0,000 m³ partout n'est ni affiché ni compté
    return out


def statut_grume(v_mere, nb, v_filles, v_aban, seuil):
    if nb == 0:
        return "En attente billonnage"
    if v_mere <= 0:
        return "Sans abattage"
    if v_filles > v_mere + 0.001:
        return "Anomalie (Filles > Mère)"
    if (v_mere - v_filles) / v_mere > seuil:
        return "Perte élevée"
    if v_aban > 0:
        return "Contient Abandon(s)"
    return "OK"


GENRE_STATUT = {"OK": "ok", "Contient Abandon(s)": "warn", "Perte élevée": "warn",
                "En attente billonnage": "neutral", "Sans abattage": "neutral",
                "Anomalie (Filles > Mère)": "bad"}


def charger_fiches(grumes: list[str]):
    """Abattage + billes filles de plusieurs grumes mères, en 2 requêtes."""
    if not grumes:
        return {}, {}
    ra = racine_sql("a.df10")
    rb = racine_sql("b.df10")
    meres = q(f"SELECT {ra} AS grume, a.df10, UPPER(TRIM(a.essence)) AS essence, TRIM(a.titre) AS titre, "
              "a.volume, a.date, a.code_barre_tige, a.code_barre_abattage, a.sequence, a.dgb, a.dpb, a.longueur, a.utmx, a.utmy "
              f"FROM abattage a WHERE {ra} = ANY(%s)", [grumes])
    filles = q(f"SELECT {rb} AS grume, b.df10, b.sequence, b.code_barre, b.longueur, b.dgb, b.dpb, b.volume, b.statut, "
               "b.situation, b.numero_lv, b.code_barre_lv, b.date_evacuation, b.camion"
               + (", b.dernier_lv, b.date_dernier_mvt " if a_dernier_lv() else " ")
               + f"FROM billonnage b WHERE {rb} = ANY(%s)", [grumes])
    m, f = {}, {}
    for r in meres:
        m.setdefault(r["grume"], r)
    for r in filles:
        f.setdefault(r["grume"], []).append(r)
    for g in f:
        f[g].sort(key=lambda r: cle_df10(r["df10"]))
    return m, f


def trouver_grumes(jetons: list[str]) -> tuple[list[str], list[str]]:
    """Grumes mères correspondant aux valeurs saisies, DANS L'ORDRE DE SAISIE.
    Retourne (grumes, valeurs_introuvables)."""
    ra, rb = racine_sql("a.df10"), racine_sql("b.df10")
    trouvees, introuvables = [], []
    for jeton in jetons:
        cle = jeton.strip().upper()
        if not cle:
            continue
        if "/" in cle:
            g = grume_mere(cle)
            lot = [g]
        else:
            lignes = q(
                f"SELECT {rb} AS g FROM billonnage b WHERE UPPER(TRIM(b.code_barre)) = %s "
                "OR UPPER(TRIM(b.code_barre_lv)) = %s OR UPPER(TRIM(b.numero_lv)) = %s "
                f"UNION SELECT {ra} FROM abattage a WHERE UPPER(TRIM(a.code_barre_tige)) = %s "
                "OR UPPER(TRIM(a.code_barre_abattage)) = %s", [cle] * 5)
            lot = sorted({r["g"] for r in lignes if r["g"]}, key=cle_df10)
            if not lot and cle.isdigit():  # carnet racine : « 54756 » -> toutes ses grumes
                lignes = q(f"SELECT {rb} AS g FROM billonnage b WHERE {rb} LIKE %s "
                           f"UNION SELECT {ra} FROM abattage a WHERE {ra} LIKE %s", [cle + "/%"] * 2)
                lot = sorted({r["g"] for r in lignes if r["g"]}, key=cle_df10)
        if not lot:
            introuvables.append(jeton)
        for g in lot:
            if g not in trouvees:
                trouvees.append(g)
    return trouvees, introuvables


def trouver_par_sequence(jetons: list[str]):
    """Billes dont la SÉQUENCE se termine par la valeur saisie (comme Billon_app).
    Retourne (grumes dans l'ordre de saisie, valeurs introuvables, codes barres trouvés, remarques)."""
    rb = racine_sql("b.df10")
    grumes, introuvables, codes, notes = [], [], set(), []
    for jeton in jetons:
        motif = "%" + jeton.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")
        lignes = q(f"SELECT {rb} AS g, b.code_barre FROM billonnage b WHERE TRIM(b.sequence) LIKE %s "
                   "ORDER BY (TRIM(b.sequence) = %s) DESC, length(TRIM(b.sequence)), b.id LIMIT %s",
                   [motif, jeton, MAX_BILLES_SEQUENCE + 1])
        if not lignes:
            introuvables.append(jeton)
            continue
        if len(lignes) > MAX_BILLES_SEQUENCE:
            notes.append(f"« {jeton} » correspond à plus de {MAX_BILLES_SEQUENCE} billes : les {MAX_BILLES_SEQUENCE} premières sont affichées (séquence exacte d'abord). Saisissez plus de chiffres pour préciser.")
            lignes = lignes[:MAX_BILLES_SEQUENCE]
        for r in lignes:
            codes.add(r["code_barre"])
            if r["g"] and r["g"] not in grumes:
                grumes.append(r["g"])
    return grumes, introuvables, codes, notes


# ---------------------------------------------------------------------------
# Affichage — briques communes
# ---------------------------------------------------------------------------
def kpi(label, valeur, unite="m³", couleur="#2D6A4F", sous=""):
    s = f'<div class="s">{e(sous)}</div>' if sous else ""
    return (f'<div class="m4-kpi" style="--c:{couleur}"><div class="l">{e(label)}</div>'
            f'<div class="v">{valeur}<small>{e(unite)}</small></div>{s}</div>')


@st.cache_data(ttl=300, show_spinner=False)
def _age_fichier_terrain() -> float | None:
    """Âge (en jours) du dernier fichier terrain préparé, d'après le journal ; None si jamais préparé ou journal indisponible."""
    try:
        r = requete("SELECT EXTRACT(EPOCH FROM (now() - MAX(quand))) / 86400 AS j FROM public.mobile_journal "
                    "WHERE evenement = 'terrain' AND detail LIKE 'données%'")
        return float(r[0]["j"]) if r and r[0]["j"] is not None else None
    except Exception:
        return None


def interrupteur_terrain() -> str:
    """Interrupteur « En ligne / Terrain » : ouvre la page terrain (secret [terrain] url). Orange si le fichier du téléphone vieillit."""
    try:
        url = str(st.secrets.get("terrain", {}).get("url", "") or "")
    except Exception:
        url = ""
    age = _age_fichier_terrain()
    vieux = age is not None and age > terrain.VALIDITE_JOURS - 1
    if not url:
        return '<span class="m4-sw off" title="Adresse terrain non configurée"><span>En ligne</span><span class="rail"><i class="kn"></i></span></span>'
    note = ""
    if vieux:
        note = ('<div class="m4-sw-note">Fichier du téléphone périmé : préparez-en un nouveau (Chargement › Terrain).</div>'
                if age >= terrain.VALIDITE_JOURS else
                '<div class="m4-sw-note">Fichier du téléphone bientôt périmé : préparez-en un nouveau (Chargement › Terrain).</div>')
    return (f'<div><a class="m4-sw{" vieux" if vieux else ""}" href="{e(url)}{"&" if "?" in url else "?"}rester=1" target="_blank" rel="noopener" '
            f'title="Ouvrir le mode terrain (sans réseau)"><span>En ligne</span><span class="rail"><i class="kn"></i></span>'
            f'<span style="opacity:.8">Terrain</span></a>{note}</div>')


def entete():
    sync = derniere_synchro()
    if sync:
        age_h = (datetime.now() - sync).total_seconds() / 3600
        classe = "m4-chip old" if age_h > 36 else "m4-chip"
        puce = f'<span class="{classe}">Données du {sync:%d/%m/%Y à %H:%M}</span>'
    else:
        puce = '<span class="m4-chip old">Date de synchronisation inconnue</span>'
    st.markdown(f'<div class="m4-hero"><div class="m4-hero-in"><div class="m4-brand">Mich4Track'
                f'<small>Suivi forestier · consultation en lecture seule</small></div>'
                f'<div class="m4-hero-row">{puce}{interrupteur_terrain()}</div></div></div>',
                unsafe_allow_html=True)


def _effacer_tous_filtres():
    for k in ("ft", "fe", "fs"):
        if k in st.session_state:
            st.session_state[k] = []

def filtres_actifs(titre: list, essence: list, sites: list | None = None):
    puces = []
    if titre:
        puces.append(("Titre : " if len(titre) == 1 else "Titres : ") + ", ".join(titre))
    if sites:
        puces.append(("Site : " if len(sites) == 1 else "Sites : ") + ", ".join(sites))
    if essence:
        puces.append(("Essence : " if len(essence) == 1 else "Essences : ") + ", ".join(essence))
    if puces:
        c1, c2 = st.columns([4, 1.3])
        c1.markdown('<div class="m4-filtres">' + "".join(f"<span>{e(p)}</span>" for p in puces) + "</div>",
                    unsafe_allow_html=True)
        c2.button("✕ Effacer", key=f"clr_filtres_{id(puces)}_{len(titre)}_{len(essence)}",
                  on_click=_effacer_tous_filtres, width="stretch")


def barres_etapes(d: dict, base: float | None = None, actif: str = "") -> str:
    """Quatre barres : abattu → billonné → évacué → usiné (échelle commune). `actif` : étape mise en avant (tri)."""
    base = base if base else max(d["abattu"], d["billonne"], d["evacue"], d["usine"], 0.0)
    lignes = []
    for lib, cle, couleur in ETAPES:
        v = d[cle]
        pct = 0.0 if base <= 0 or v <= 0 else max(2.0, min(100.0, v / base * 100))
        lignes.append(f'<div class="m4-pl{" on" if cle == actif else ""}"><span class="m4-pl-l">{lib}</span>'
                      f'<span class="m4-pl-t"><i style="width:{pct:.1f}%;background:{couleur}"></i></span>'
                      f'<span class="m4-pl-v">{fr(v)}</span></div>')
    return '<div class="m4-pipe">' + "".join(lignes) + "</div>"


def puces_indicateurs(d: dict, nb_lv: int | None = None) -> str:
    p = []
    if d["n_grumes_b"]:
        if d["perte"] >= 0:
            p.append(f'<span class="m4-c {"bad" if d["perte_pct"] > 10 else "wood"}">Perte {fr(d["perte"])} m³ · {d["perte_pct"]:.1f} %</span>')
        else:
            p.append(f'<span class="m4-c warn">Excédent {fr(-d["perte"])} m³</span>')
    p.append(f'<span class="m4-c ok">Évacuation {d["taux_evac"]:.1f} %</span>')
    if nb_lv:
        p.append(f'<span class="m4-c wood">{nb_lv} LV</span>')
    if d["abandon"] > 0:
        p.append(f'<span class="m4-c warn">Abandon {fr(d["abandon"])} m³</span>')
    return '<div class="m4-chips">' + "".join(p) + "</div>"


def carte_total(d: dict, libelle: str, actif: str = "", nb_lv: int | None = None) -> str:
    return (f'<div class="m4-total"><div class="m4-total-h"><b>Total</b><span>{e(libelle)}</span></div>'
            f'{barres_etapes(d, actif=actif)}{puces_indicateurs(d, nb_lv)}</div>')


def ligne_detail(nom: str, d: dict, couleur: str, base: float) -> str:
    vol = d["billonne"] or d["abattu"]
    pct = max(2.0, min(100.0, vol / base * 100)) if base > 0 and vol > 0 else 0
    return (f'<div class="m4-sub"><div class="m4-sub-top"><span class="m4-dot" style="background:{couleur}"></span>'
            f'<b>{e(nom)}</b><span class="v">{fr(d["billonne"])} <small style="font-weight:500;color:#5A6F60">m³ exploité</small></span></div>'
            f'<div class="m4-gauge"><i style="width:{pct:.0f}%;background:{couleur}"></i></div>'
            f'<div class="m4-ess-sub">abattu {fr(d["abattu"])} · évacué {fr(d["evacue"])} · usiné {fr(d["usine"])} m³'
            f'{" · perte " + fr(d["perte"]) + " m³" if d["n_grumes_b"] and d["perte"] > 0 else ""}</div></div>')


LIB_MESURE = {"billonne": "exploité", "abattu": "abattu", "evacue": "évacué", "usine": "usiné", "perte": "de perte"}


def carte_rapport(nom: str, d: dict, couleur: str, detail_titre: str, detail: list[tuple[str, dict]],
                  couleur_detail, mesure: str = "billonne", rang: int | None = None, nb_lv: int | None = None) -> str:
    """Carte dépliable : résumé (étapes + indicateurs) ; au toucher, la ventilation.
    Le chiffre de l'en-tête suit la mesure du tri (exploité, abattu, évacué, usiné, perte)."""
    sous_base = max((max(x["billonne"], x["abattu"]) for _, x in detail), default=0.0)
    corps = "".join(ligne_detail(n, x, couleur_detail(n), sous_base) for n, x in detail)
    valeur = f'{d["perte"]:+.3f}'.replace(".", ",") if mesure == "perte" else fr(d[mesure])
    rg = f'<span class="m4-rank">{rang}</span>' if rang else ""
    return (f'<details class="m4-card"><summary><div class="m4-card-top">{rg}<span class="m4-dot" style="background:{couleur}"></span>'
            f'<b>{e(nom)}</b><span class="m4-card-vol">{valeur} <small>m³ {LIB_MESURE[mesure]}</small></span>'
            f'<span class="m4-chev"></span></div>{barres_etapes(d, actif=mesure)}{puces_indicateurs(d, nb_lv)}</summary>'
            f'<div class="m4-body"><div class="m4-body-h">{e(detail_titre)}</div>{corps}</div></details>')


def telecharger(df: pd.DataFrame, nom_fichier: str, cle: str):
    csv = df.round(3).to_csv(index=False, sep=";", decimal=",", float_format="%.3f").encode("utf-8-sig")
    st.download_button("Télécharger ce rapport (CSV)", csv, file_name=nom_fichier, mime="text/csv",
                       width="stretch", key=cle)


def _cfg_dgb(df: pd.DataFrame) -> dict:
    """Colonnes DGB / DPB : affichées sans zéros inutiles (70 et non 70.000000) quand elles sont numériques."""
    return {c: st.column_config.NumberColumn(format="%g") for c in ("DGB", "DPB")
            if c in df.columns and pd.api.types.is_numeric_dtype(df[c])}


def _num(v):
    """DGB / DPB : nombres propres (Decimal -> float), texte laissé tel quel, vide -> None."""
    if v is None or str(v).strip() == "":
        return None
    try:
        return float(v)
    except (TypeError, ValueError):
        return str(v)


COLS_EXACTES = ("DF10", "Code barre", "Séq.", "N° LV")


def styler_exacts(df: pd.DataFrame, exacts, surligner: set | None = None):
    """Lignes dont DF10, code barre, séquence ou N° LV est EXACTEMENT une valeur saisie : en gras (et surlignées)."""
    ex = {str(x).strip().upper() for x in (exacts or []) if str(x).strip()}
    sur = surligner or set()

    def style(ligne):
        exact = any(str(ligne[c] or "").strip().upper() in ex for c in COLS_EXACTES if c in ligne.index) if ex else False
        fond = exact or (ligne.get("Code barre") in sur)
        css = ("background-color:#D8F3DC;" if fond else "") + ("font-weight:700" if exact else "")
        return [css] * len(ligne)
    fmt = {"Long. (m)": "{:.1f}", "Vol. (m³)": "{:.3f}", **{c: "{:g}" for c in _cfg_dgb(df)}}
    return df.style.apply(style, axis=1).format(fmt, na_rep="")


def a_des_exacts(df: pd.DataFrame, exacts) -> bool:
    ex = {str(x).strip().upper() for x in (exacts or []) if str(x).strip()}
    return bool(ex) and any(df[c].astype(str).str.strip().str.upper().isin(ex).any() for c in COLS_EXACTES if c in df.columns)


# ---------------------------------------------------------------------------
# Chaîne de traçabilité : inventaire → abattage → billonnage → évacuation (LV) → usine
# ---------------------------------------------------------------------------
@st.cache_data(ttl=TTL_DONNEES, show_spinner=False)
def _inventaire_pour(cb: str, seq: str, titre: str):
    """(ligne d'inventaire | None, table disponible). Clé = code barre de la tige ; à défaut séquence + titre."""
    cols = "code_barre, sequence, essence, diametre, bloc, qualite, utmx, utmy, zone"
    try:
        if cb:
            r = q(f"SELECT {cols} FROM inventaire WHERE UPPER(TRIM(code_barre)) = %s LIMIT 1", [cb.strip().upper()])
            if r:
                return r[0], True
        if seq and titre:
            r = q(f"SELECT {cols} FROM inventaire WHERE TRIM(sequence) = %s AND TRIM(titre) = %s LIMIT 2", [seq.strip(), titre.strip()])
            if len(r) == 1:
                return r[0], True
        return None, True
    except Exception:
        return None, False


@st.cache_data(ttl=TTL_DONNEES, show_spinner=False)
def _usine_pour(cbs: tuple) -> dict:
    """Billes passées en usine : code barre -> ligne de production."""
    if not cbs:
        return {}
    try:
        lignes = q("SELECT UPPER(TRIM(code_barre)) AS cb, lot, date_usinage, volume FROM production "
                   "WHERE UPPER(TRIM(code_barre)) = ANY(%s)", [[c.strip().upper() for c in cbs]])
    except Exception:
        return {}
    return {r["cb"]: r for r in lignes}


@st.cache_data(ttl=TTL_DONNEES, show_spinner=False)
def _sites_billes(cbs: tuple) -> dict:
    """Site (Batouri / Sengbot…) de chaque bille ; vide tant que la colonne SITE n'existe pas en base."""
    if not cbs:
        return {}
    try:
        return {r["cb"]: r["site"] for r in q("SELECT UPPER(TRIM(code_barre)) AS cb, UPPER(TRIM(site)) AS site FROM billonnage "
                                              "WHERE UPPER(TRIM(code_barre)) = ANY(%s) AND TRIM(COALESCE(site,'')) <> ''",
                                              [[c.strip().upper() for c in cbs]])}
    except Exception:
        return {}


def _lot_affiche(site: str, lot) -> str:
    """Batouri : le lot est le N° de contrat, affiché avec le préfixe « D0 » ; Sengbot (ou autre) : N° de lot tel quel."""
    lot = str(lot or "").strip()
    if not lot:
        return ""
    return (f"N° contrat <b>D0{e(lot)}</b>" if (site or "").upper() == "BATOURI" else f"Lot <b>{e(lot)}</b>")


def _au_parc_usine(r: dict) -> bool:
    sit = str(r.get("situation") or "").upper()
    return "PARC" in sit and "USINE" in sit


@st.cache_data(ttl=TTL_DONNEES, show_spinner=False)
def _chauffeur_pour(cb: str) -> str:
    try:
        r = q("SELECT chauffeur FROM billonnage WHERE UPPER(TRIM(code_barre)) = %s LIMIT 1", [cb.strip().upper()])
        return str(r[0]["chauffeur"] or "").strip() if r else ""
    except Exception:
        return ""


def _jour(d) -> str:
    return d.strftime("%d/%m/%Y") if hasattr(d, "strftime") else (str(d) if d else "")


def _etape(rang: int, titre: str, genre: str, etat: str, lignes: list[str]) -> str:
    corps = "".join(f'<div class="m4-et-l">{l}</div>' for l in lignes if l)
    return (f'<div class="m4-et {genre}"><div class="m4-et-pt">{rang}</div><div class="m4-et-c">'
            f'<div class="m4-et-t">{e(titre)}<span>{e(etat)}</span></div>{corps}</div></div>')


def _gn(v):
    """Diamètre / DGB / DPB sans décimale inutile (120.0 -> 120)."""
    x = _num(v)
    return f"{x:g}" if isinstance(x, float) else x


# ---------------------------------------------------------------------------
# Position d'une tige (inventaire / abattage) : coordonnées UTM + carte d'un point
# ---------------------------------------------------------------------------
SEUIL_ECART_M = 50        # écart inventaire ↔ abattage au-delà duquel on le signale (précision GPS courante : 5–10 m)


def _zone_utm(texte) -> tuple[int, bool]:
    """« 33N », « 32 », « Zone 32 S » -> (33, True)… Défaut : zone 33 Nord (Cameroun est)."""
    m = re.search(r"(\d{1,2})\s*([NSns])?", str(texte or ""))
    if m and 1 <= int(m.group(1)) <= 60:
        return int(m.group(1)), (m.group(2) or "N").upper() != "S"
    return carte_abattage.ZONE_UTM_DEFAUT, True


def _position(x, y, zone_txt="") -> dict | None:
    """Position UTM valide (plausible) -> {"x","y","zone","nord","lat","lon"} ; sinon None."""
    try:
        xf, yf = carte_abattage._nombre(x), carte_abattage._nombre(y)
    except Exception:
        return None
    if not carte_abattage._position_plausible(xf, yf):
        return None
    zone, nord = _zone_utm(zone_txt)
    lat, lon = carte_abattage.utm_vers_wgs84(xf, yf, zone, nord)
    return {"x": xf, "y": yf, "zone": zone, "nord": nord, "lat": lat, "lon": lon}


def _utm_txt(p: dict) -> str:
    n = lambda v: f"{round(v):,}".replace(",", " ")
    return f"X {n(p['x'])} · Y {n(p['y'])} · UTM {p['zone']}{'N' if p['nord'] else 'S'}"


def _ecart_m(p1: dict, p2: dict) -> float | None:
    """Distance (m) entre deux positions de même zone ; None si zones différentes."""
    if (p1["zone"], p1["nord"]) != (p2["zone"], p2["nord"]):
        return None
    return math.hypot(p1["x"] - p2["x"], p1["y"] - p2["y"])


PAGE_POINT = """<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.css">
<style>
html,body{margin:0;height:100%;font-family:system-ui,-apple-system,Segoe UI,sans-serif;color:#14251C;background:#F1F6EF}
#m{height:calc(100% - var(--bas,0px));width:100%}
#bas{position:absolute;left:0;right:0;bottom:0;background:#fff;border-top:1px solid #D3DFD3;padding:.45rem .7rem;font-size:.78rem;line-height:1.5;z-index:500}
.pt{display:flex;align-items:center;gap:.5rem;flex-wrap:wrap}.pt b{font-weight:800}
.pt i{width:.8rem;height:.8rem;border-radius:50%;display:inline-block;border:2px solid #fff;box-shadow:0 0 0 1px #14251C}
.pt .ec{color:#B5651D;font-weight:700}
.rep{background:none;border:none}.rep span{display:block;width:1.5rem;height:1.5rem;border-radius:50% 50% 50% 0;transform:rotate(-45deg);
  border:2px solid #fff;box-shadow:0 2px 6px rgba(0,0,0,.55)}.rep span::after{content:"";position:absolute;left:.42rem;top:.42rem;width:.45rem;height:.45rem;border-radius:50%;background:#fff}
.foc span{outline:3px solid rgba(255,255,255,.75);outline-offset:2px}
</style></head><body><div id="m"></div><div id="bas"></div>
<script src="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.js"></script>
<script>
const D = __DATA__;
const bas = document.getElementById('bas');
bas.innerHTML = D.points.map(p => '<div class="pt"><i style="background:'+p.couleur+'"></i><b>'+p.nom+'</b>'+(p.detail ? ' <span style="color:#5B6B61">'+p.detail+'</span>' : '')+
  '</div>'
  + '<div style="color:#5B6B61;font-size:.72rem;margin:0 0 .25rem 1.3rem">'+p.utm+' · '+p.lat.toFixed(6)+', '+p.lon.toFixed(6)+'</div>').join('') + (D.ecart ? '<div class="ec pt">'+D.ecart+'</div>' : '');
document.documentElement.style.setProperty('--bas', bas.offsetHeight + 'px');
const map = L.map('m', {zoomControl:true});
const esri = L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}', {maxZoom:19, attribution:'© Esri, Maxar, Earthstar Geographics'});
const osm = L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {maxZoom:19, attribution:'© OpenStreetMap'});
esri.addTo(map);
L.control.layers({'Satellite': esri, 'Plan': osm}, null, {position:'topright'}).addTo(map);
L.control.scale({imperial:false}).addTo(map);
const bornes = [];
D.contours.forEach(c => c.polys.forEach(poly => { const l = L.polygon(poly, {color:'#FFD166', weight:2, fill:false, dashArray:'6 4'}).addTo(map); if (D.points.length > 1 || !D.points.length) bornes.push(l.getBounds()); }));
const marques = D.points.map(p => {
  const ic = L.divIcon({className:'rep'+(p.focus?' foc':''), html:'<span style="background:'+p.couleur+'"></span>', iconSize:[24,24], iconAnchor:[12,24]});
  const mk = L.marker([p.lat, p.lon], {icon: ic}).addTo(map).bindPopup('<b>'+p.nom+'</b><br>'+p.utm);
  if (p.focus) mk.openPopup();
  return mk;
});
if (D.points.length === 2) L.polyline([[D.points[0].lat, D.points[0].lon], [D.points[1].lat, D.points[1].lon]], {color:'#fff', weight:2, dashArray:'4 6'}).addTo(map);
const foc = D.points.find(p => p.focus) || D.points[0];
if (D.points.length === 2 && D.ecart_m !== null && D.ecart_m < 400) map.fitBounds(L.latLngBounds(D.points.map(p => [p.lat, p.lon])), {padding:[60,60], maxZoom:19});
else map.setView([foc.lat, foc.lon], 18);
</script></body></html>"""


def html_point(titre: str, points: list[dict], contours: list, ecart_txt: str = "", ecart_m=None) -> str:
    """Page Leaflet autonome : un ou deux points (inventaire / abattage) sur fond satellite, avec le contour du titre."""
    cont = []
    if contours:
        try:
            cont = carte_abattage.preparer_donnees(titre, contours, [])["contours"]
        except Exception:
            cont = []
    data = {"points": points, "contours": cont, "ecart": ecart_txt, "ecart_m": ecart_m}
    return PAGE_POINT.replace("__DATA__", json.dumps(data, ensure_ascii=False).replace("</", "<\\/"))


@st.dialog("Position sur la carte", width="large")
def dialogue_position(titre: str, points: list[dict], ecart_txt: str, ecart_m):
    contours = []
    try:
        contours = carte_abattage.contours_pour_titre(DOSSIER_CONTOURS, titre) if titre else []
    except Exception:
        contours = []
    st.iframe(html_point(titre, points, contours, ecart_txt, ecart_m), height=600)
    st.caption("Fond satellite (Esri) · pointillés jaunes : contour du titre")


def positions_tige(mere: dict | None, inv: dict | None) -> dict:
    """Positions inventaire / abattage d'une tige, et écart entre les deux."""
    zone_inv = (inv or {}).get("zone", "")
    p_inv = _position((inv or {}).get("utmx"), (inv or {}).get("utmy"), zone_inv) if inv else None
    p_ab = _position((mere or {}).get("utmx"), (mere or {}).get("utmy"), zone_inv) if mere else None
    ecart = _ecart_m(p_inv, p_ab) if p_inv and p_ab else None
    return {"inv": p_inv, "abat": p_ab, "ecart": ecart}


def boutons_position(grume: str, mere: dict | None, inv: dict | None):
    """Coordonnées de la tige (celles de l'inventaire, à défaut celles de l'abattage) : le bouton ouvre la carte sur ce point."""
    pos = positions_tige(mere, inv)
    p = pos["inv"] or pos["abat"]
    if not p:
        return
    titre = str((mere or {}).get("titre") or "")
    detail = (f"{str(inv.get('essence') or '').upper()} · Ø {_gn(inv.get('diametre')) or '–'} cm" if inv and pos["inv"]
              else (f"{mere.get('df10') or ''} · {mere.get('essence') or ''}" if mere else ""))
    pt = {"cle": "tige", "nom": f"Tige {(inv or mere or {}).get('code_barre') or (mere or {}).get('code_barre_tige') or ''}".strip(),
          "couleur": "#2D6A4F", "utm": _utm_txt(p), "lat": p["lat"], "lon": p["lon"], "detail": detail, "focus": True}
    if st.button(pt["utm"].split(" · UTM")[0], icon=":material/location_on:", key=f"loc_{grume}", width="stretch",
                 help=f"Afficher cette position sur la carte ({pt['utm']})"):
        dialogue_position(titre, [pt], "", None)


def _ligne_position_abattage(mere: dict, inv: dict | None) -> list[str]:
    """La position est celle de l'inventaire (reprise à l'abattage). On ne la répète que si elle manque ou diffère."""
    pos = positions_tige(mere, inv)
    if pos["abat"] and not pos["inv"]:
        return [f"Position : {e(_utm_txt(pos['abat']))}"]
    if pos["ecart"] is not None and pos["ecart"] > SEUIL_ECART_M:
        return [f'<b style="color:#B5651D">Position d\'abattage différente de l\'inventaire ({pos["ecart"]:.0f} m)</b>']
    return []


def chaine_tracabilite_html(grume: str, mere: dict | None, lignes: list[dict], exacts) -> str:
    """Chaîne épurée : valeurs seules (pas d'intitulés évidents pour un professionnel), ✅/❌ pour le statut, 📍 pour la situation."""
    ex = {str(x).strip().upper() for x in (exacts or []) if str(x).strip()}

    def vise(r):
        return any(str(r.get(c) or "").strip().upper() in ex for c in ("df10", "code_barre", "sequence", "numero_lv", "code_barre_lv")) if ex else False
    cibles = [r for r in lignes if vise(r)]
    bille = cibles[0] if len(cibles) == 1 else None
    etapes = []
    inv = None
    # 1 — Inventaire
    if mere:
        inv, dispo = _inventaire_pour(str(mere.get("code_barre_tige") or ""), str(mere.get("sequence") or ""), str(mere.get("titre") or ""))
        pos_inv = _position(inv.get("utmx"), inv.get("utmy"), inv.get("zone")) if inv else None
        if dispo:
            if inv:
                carac = [f"<b>{e(str(inv.get('essence') or '').upper())}</b>", f"Ø {e(_gn(inv.get('diametre')) or '–')} cm"]
                carac += [e(inv[c]) for c in ("bloc", "qualite") if inv.get(c)]
                etapes.append(_etape(1, "Inventaire", "ok", "Recensé", [" · ".join(carac), " · ".join(x for x in (e(inv.get("code_barre") or ""), e(_utm_txt(pos_inv)) if pos_inv else "Position non renseignée") if x)]))
            else:
                etapes.append(_etape(1, "Inventaire", "warn", "Hors inventaire", ["Cette tige abattue ne figure pas dans l'inventaire du titre."]))
    # 2 — Abattage
    if mere:
        dims = (f"DGB {_gn(mere.get('dgb')) or '–'} · DPB {_gn(mere.get('dpb')) or '–'} · "
                f"{fr(mere.get('longueur'), 1)} m · {fr(mere.get('volume'))} m³")
        etapes.append(_etape(2, "Abattage", "ok", f"Abattue le {_jour(mere.get('date'))}" if mere.get("date") else "Abattue", [
            " · ".join(x for x in (f"<b>{e(mere.get('df10') or grume)}</b>", e(str(mere.get('essence') or '')), e(mere.get("code_barre_abattage") or "")) if x), dims,
            *_ligne_position_abattage(mere, inv)]))
    else:
        etapes.append(_etape(2, "Abattage", "bad", "Introuvable", ["Aucune grume mère enregistrée pour ce code : billes sans abattage."]))
    # 3 — Billonnage
    if lignes:
        v_tot = sum(float(r["volume"] or 0) for r in lignes)
        ab = [r for r in lignes if str(r["statut"] or "").strip().upper() == "ABANDON"]
        v_ab = sum(float(r["volume"] or 0) for r in ab)
        l3 = [f"<b>{len(lignes)} bille(s)</b> · {fr(v_tot - v_ab)} m³ exploités" + (f" · <b>{len(ab)} abandon(s)</b> ({fr(v_ab)} m³)" if ab else "")]
        if bille:
            abandon = str(bille.get("statut") or "").strip().upper() == "ABANDON"
            l3.append(f"<b>{e(bille['df10'])}</b> · {e(bille['code_barre'] or '–')} {'❌' if abandon else '✅'} · "
                      f"DGB {_gn(bille['dgb']) or '–'} · DPB {_gn(bille['dpb']) or '–'} · {fr(bille.get('longueur'), 1)} m · {fr(bille['volume'])} m³")
        etapes.append(_etape(3, "Billonnage", "warn" if ab else "ok", "Billonnée", l3))
    else:
        etapes.append(_etape(3, "Billonnage", "vide", "En attente", ["Pas encore de billes filles pour cette grume."]))
    # 4 — Évacuation / LV
    if lignes:
        if bille:
            lv = str(bille.get("numero_lv") or "").strip()
            sit = f"📍 {e(bille.get('situation') or '–')}"
            if lv:
                chauffeur = _chauffeur_pour(str(bille["code_barre"] or ""))
                cb_lv = str(bille.get("code_barre_lv") or "").strip()
                transport = " · ".join(x for x in (e(bille.get("camion") or ""), e(chauffeur), e(cb_lv)) if x)
                etapes.append(_etape(4, "Évacuation (LV)", "ok", f"LV N° {lv}", [f"Évacuée le {_jour(bille.get('date_evacuation')) or '–'} · {sit}", transport]))
            else:
                etapes.append(_etape(4, "Évacuation", "vide", "Au parc forêt", []))
        else:
            evac = [r for r in lignes if str(r.get("numero_lv") or "").strip()]
            lvs = sorted({str(r["numero_lv"]).strip() for r in evac})
            etapes.append(_etape(4, "Évacuation (LV)", "ok" if len(evac) == len(lignes) else ("warn" if evac else "vide"),
                                 f"{len(evac)} / {len(lignes)} évacuée(s)",
                                 [("LV " + e(", ".join(lvs[:8])) + (" …" if len(lvs) > 8 else "")) if lvs else "Aucune bille évacuée pour l'instant."]))
    # 5 — Usine : Sengbot = site seul ; Batouri = site + contrat (lot précédé de « D0 »)
    if lignes:
        base = [bille] if bille else [r for r in lignes if str(r["statut"] or "").strip().upper() != "ABANDON"]
        cbs = tuple(str(r["code_barre"] or "") for r in base if r["code_barre"])
        prod, sites = _usine_pour(cbs), _sites_billes(cbs)
        cle = lambda r: str(r["code_barre"] or "").strip().upper()
        recues = [r for r in base if cle(r) in prod or _au_parc_usine(r)]
        groupes: dict[str, set] = {}
        for r in recues:
            site = sites.get(cle(r), "")
            lot = str(prod[cle(r)]["lot"] or "").strip() if cle(r) in prod else ""
            groupes.setdefault(site, set())
            if lot:
                groupes[site].add(lot)
        l5 = []
        for site, lots in sorted(groupes.items()):
            if site == "BATOURI":
                l5.append("BATOURI" + (" · Contrat N° " + ", ".join("D0" + l for l in sorted(lots)) if lots else ""))
            elif site:
                l5.append(site)
            elif lots:
                l5.append("Lot " + ", ".join(sorted(lots)))
        if bille:
            etat = "Reçue à l'usine" if recues else "Pas encore à l'usine"
            genre = "ok" if recues else "vide"
        else:
            etat = f"{len(recues)} / {len(base)} reçue(s) à l'usine"
            genre = "ok" if base and len(recues) == len(base) else ("warn" if recues else "vide")
        etapes.append(_etape(5, "Usine", genre, etat, [e(x) for x in l5]))
    return '<div class="m4-chaine">' + "".join(etapes) + "</div>"


def afficher_fiche(grume: str, meres: dict, filles: dict, seuil: float, surligner: set | None = None, exacts=None):
    mere = meres.get(grume)
    lignes = filles.get(grume, [])
    v_mere = float(mere["volume"] or 0) if mere else 0.0
    v_filles = sum(float(r["volume"] or 0) for r in lignes)
    v_aban = sum(float(r["volume"] or 0) for r in lignes if str(r["statut"] or "").strip().upper() == "ABANDON")
    st_g = statut_grume(v_mere, len(lignes), v_filles, v_aban, seuil)
    essence = (mere or {}).get("essence") or ""
    titre = (mere or {}).get("titre") or ""
    with st.container(border=True):
        if st.button("Partager", icon=":material/ios_share:", key=f"shfiche_{grume}"):
            dialogue_fiche(grume, mere, lignes, seuil)
        tete = (f'<div class="m4-fiche-t"><b>{e(grume)}</b>{badge(essence, "neutral") if essence else ""}'
                f'{badge(st_g, GENRE_STATUT.get(st_g, "neutral"))}</div>')
        sous = " · ".join(x for x in (titre, f"abattue le {mere['date']:%d/%m/%Y}" if mere and mere.get("date") else "") if x)
        st.markdown(tete + (f'<div class="m4-fiche-s">{e(sous)}</div>' if sous else ""), unsafe_allow_html=True)
        perte = (v_mere - v_filles) if lignes else 0.0
        n_exploitees = sum(1 for r in lignes if str(r["statut"] or "").strip().upper() != "ABANDON")
        st.markdown('<div class="m4-kpis three">'
                    + kpi("Abattu", fr(v_mere), couleur="#2D6A4F")
                    + kpi("Exploité", fr(v_filles - v_aban), couleur="#52B788", sous=f"{n_exploitees} bille(s)")
                    + kpi("Perte", f"{perte:+.3f}".replace(".", ","), couleur="#B94A44" if perte > 0 else "#2D6A4F")
                    + '</div>', unsafe_allow_html=True)
        with st.expander("Chaîne de traçabilité", icon=":material/account_tree:", expanded=bool(exacts)):
            st.markdown(chaine_tracabilite_html(grume, mere, lignes, exacts), unsafe_allow_html=True)
            if mere:
                inv_, _ok = _inventaire_pour(str(mere.get("code_barre_tige") or ""), str(mere.get("sequence") or ""), str(mere.get("titre") or ""))
                boutons_position(grume, mere, inv_)
        if not lignes:
            st.markdown('<div class="m4-vide">Pas encore de billes filles pour cette grume.</div>', unsafe_allow_html=True)
            return
        df = pd.DataFrame([{
            "DF10": r["df10"], "Code barre": r["code_barre"], "Séq.": r["sequence"] or "",
            "DGB": _num(r["dgb"]), "DPB": _num(r["dpb"]),
            "Long. (m)": float(r["longueur"] or 0), "Vol. (m³)": float(r["volume"] or 0),
            "Situation": r["situation"] or "", "Statut": icone_statut(r["statut"]),
            "N° LV": r["numero_lv"] or "", "Évacuée le": r["date_evacuation"], "Camion": r["camion"] or "",
            **({"Dernier LV": r.get("dernier_lv") or "", "Dernier mvt le": (r["date_dernier_mvt"].strftime("%d/%m/%Y") if r.get("date_dernier_mvt") is not None and hasattr(r["date_dernier_mvt"],"strftime") else "")} if "dernier_lv" in r else {}),
        } for r in lignes])
        cfg = {
            "DF10": st.column_config.TextColumn(pinned=True),
            "Long. (m)": st.column_config.NumberColumn(format="%.1f"),   # longueur : 1 décimale
            "Vol. (m³)": st.column_config.NumberColumn(format="%.3f"),   # volume : 3 décimales
            "Évacuée le": st.column_config.DateColumn(format="DD/MM/YYYY"),
            **_cfg_dgb(df),
        }
        # Version cartes pour écrans mobiles (sans défilement horizontal)
        ex_set = {str(x).strip().upper() for x in (exacts or []) if str(x).strip()}
        sur_set = surligner or set()
        cartes_billes = []
        for r in lignes:
            df10_b = str(r["df10"] or "")
            cb_b = str(r["code_barre"] or "")
            seq_b = str(r["sequence"] or "")
            lv_b = str(r["numero_lv"] or "")
            est_exact = any(val.strip().upper() in ex_set for val in (df10_b, cb_b, seq_b, lv_b) if val) or (cb_b in sur_set)
            cls_card = "m4-bille-card exact" if est_exact else "m4-bille-card"
            dims = f"DGB { _num(r['dgb']) or '–'} · DPB {_num(r['dpb']) or '–'} · Long. {float(r['longueur'] or 0):.1f} m"
            ev_txt = f" · LV {e(lv_b)}" if lv_b else ""
            cam_txt = f" ({e(r['camion'])})" if r.get("camion") else ""
            cartes_billes.append(
                f'<div class="{cls_card}">'
                f'<div class="m4-bille-head">'
                f'<span class="m4-copy-chip" onclick="navigator.clipboard&&navigator.clipboard.writeText(\'{e(df10_b)}\')" title="Toucher pour copier">{e(df10_b)} 📋</span>'
                f'<span>{fr(r["volume"])} m³ {icone_statut(r["statut"])}</span></div>'
                f'<div class="m4-bille-meta">Séq. <b>{e(seq_b or "—")}</b> · CB {e(cb_b or "—")}<br>'
                f'{dims}<br>Situation : <b>{e(r["situation"] or "—")}</b>{ev_txt}{cam_txt}</div></div>'
            )
        st.markdown('<div class="m4-bille-cards">' + "".join(cartes_billes) + '</div>', unsafe_allow_html=True)
        st.markdown('<div class="m4-bille-table-pc">', unsafe_allow_html=True)
        if surligner or a_des_exacts(df, exacts):
            st.dataframe(styler_exacts(df, exacts, surligner), hide_index=True, width="stretch", column_config=cfg)
        else:
            st.dataframe(df, hide_index=True, width="stretch", column_config=cfg)
        st.markdown('</div>', unsafe_allow_html=True)


# ---------------------------------------------------------------------------
# Bilan par titre et par essence : cartes (téléphone), tableau (PC), Excel, CSV
# ---------------------------------------------------------------------------
SANS_SITE = "SANS SITE"
_CLES_BILAN = ("abattu", "billonne", "abandon", "evacue", "usine")


def _cle_nat(t: str) -> list:
    return [int(c) if c.isdigit() else c.lower() for c in re.split(r"(\d+)", t or "")]


def _cle_site(s: str) -> tuple:
    return (s == SANS_SITE, _cle_nat(s))


def sites_filtres() -> list:
    return list(st.session_state.get("fs") or [])


def charger_bilan_sites() -> dict:
    """(essence, titre) -> {site: [évacué, usiné, stock du parc de rupture]} (m³) d'après le site enregistré sur chaque bille ;
    {} sans colonne site. Stock du site = billes actuellement en « Parc de rupture » à ce site."""
    if not liste_sites():
        return {}
    res: dict = {}
    for r in q("SELECT COALESCE(UPPER(TRIM(b.essence)),'') AS essence, COALESCE(TRIM(b.titre),'') AS titre, "
               "COALESCE(NULLIF(UPPER(TRIM(b.site)),''), 'SANS SITE') AS site, "
               "COALESCE(SUM(b.volume) FILTER (WHERE UPPER(TRIM(COALESCE(b.situation,''))) = ANY(%s) "
               "AND UPPER(TRIM(COALESCE(b.statut,''))) <> 'ABANDON'),0) AS v, "
               "COALESCE(SUM(b.volume) FILTER (WHERE UPPER(TRIM(COALESCE(b.situation,''))) = 'PARC DE RUPTURE' "
               "AND UPPER(TRIM(COALESCE(b.statut,''))) <> 'ABANDON'),0) AS stock FROM billonnage b GROUP BY 1, 2, 3",
               [SITUATIONS_EVACUEES]):
        c = res.setdefault((r["essence"], r["titre"]), {}).setdefault(r["site"], [0.0, 0.0, 0.0])
        c[0], c[2] = float(r["v"]), float(r["stock"])
    for r in q("SELECT COALESCE(UPPER(TRIM(b.essence)),'') AS essence, COALESCE(TRIM(b.titre),'') AS titre, "
               "COALESCE(NULLIF(UPPER(TRIM(b.site)),''), 'SANS SITE') AS site, COALESCE(SUM(b.volume),0) AS v "
               "FROM billonnage b WHERE UPPER(TRIM(COALESCE(b.situation,''))) = 'PARC USINE' "
               "AND UPPER(TRIM(COALESCE(b.statut,''))) <> 'ABANDON' GROUP BY 1, 2, 3"):
        res.setdefault((r["essence"], r["titre"]), {}).setdefault(r["site"], [0.0, 0.0, 0.0])[1] = float(r["v"])
    return res


def charger_pieds_autorises() -> dict:
    """(essence, titre) -> pieds autorisés par le permis ; {} si la table Permis n'existe pas encore."""
    try:
        return {(r["essence"], r["titre"]): int(r["n"]) for r in q(
            "SELECT UPPER(TRIM(essence)) AS essence, COALESCE(TRIM(titre),'') AS titre, COALESCE(SUM(pied),0) AS n "
            "FROM permis WHERE TRIM(COALESCE(essence,'')) <> '' GROUP BY 1, 2")}
    except psycopg2.errors.UndefinedTable:
        return {}


def construire_bilan(df: pd.DataFrame, sites_sel: list | None = None) -> dict:
    """Structure commune aux quatre rendus : {'sites': [...], 'titres': [{titre, lignes, total}], 'general': {...}}.
    Évacué / usiné sont ventilés par site ; le stock (exploité − évacué total) et les volumes amont ne dépendent pas du site."""
    if df.empty:
        return {"sites": [], "titres": [], "general": None}
    par_site = charger_bilan_sites()
    auto = charger_pieds_autorises()
    sites_sel = [s.upper() for s in (sites_sel or [])]
    toutes = set()
    for sd in par_site.values():
        toutes.update(s for s, v in sd.items() if max(v) > 0.0005)
    sites = sorted((s for s in toutes if not sites_sel or s in sites_sel), key=_cle_site)

    def fabrique(x, cles_site, auto_n):
        d = {"n": int(x["n_abattu"]), "auto": auto_n, "abattu": x["abattu"], "prepare": x["billonne"] + x["abandon"],
             "exploite": x["billonne"], "stock": x["billonne"] - x["evacue"], "sites": {}}
        for s in sites:
            d["sites"][s] = list(cles_site.get(s, [0.0, 0.0, 0.0]))
        d["ev_tot"] = sum(v[0] for v in d["sites"].values())
        d["us_tot"] = sum(v[1] for v in d["sites"].values())
        d["st_tot"] = sum(v[2] for v in d["sites"].values())
        d["depasse"] = auto_n is not None and d["n"] > auto_n
        return d

    titres, gen_cles = [], []
    for titre in sorted(df["titre"].unique(), key=_cle_nat):
        sous = df[df["titre"] == titre]
        ess = [(n, t) for n, t in agreger(sous, "essence") if any(abs(t[c]) > 0.0005 for c in _CLES_BILAN)]
        if not ess:
            continue
        ess.sort(key=lambda x: (-x[1]["billonne"], -x[1]["abattu"]))
        lignes = []
        for n, x in ess:
            lignes.append({"essence": n or "—", **fabrique(x, par_site.get((n, titre), {}), auto.get((n, titre)))})
        a_ok = [l["auto"] for l in lignes if l["auto"] is not None]
        tt = totaux(sous)
        total = fabrique(tt, {}, sum(a_ok) if a_ok else None)
        for s in sites:
            total["sites"][s] = [sum(l["sites"][s][k] for l in lignes) for k in range(3)]
        total["ev_tot"], total["us_tot"], total["st_tot"] = (sum(l["ev_tot"] for l in lignes), sum(l["us_tot"] for l in lignes),
                                                              sum(l["st_tot"] for l in lignes))
        total["depasse"] = any(l["depasse"] for l in lignes)
        titres.append({"titre": titre or "—", "lignes": lignes, "total": total})
    general = None
    if len(titres) > 1:
        tt = totaux(df[df["titre"].isin([t["titre"] if t["titre"] != "—" else "" for t in titres])])
        a_ok = [t["total"]["auto"] for t in titres if t["total"]["auto"] is not None]
        general = fabrique(tt, {}, sum(a_ok) if a_ok else None)
        for s in sites:
            general["sites"][s] = [sum(t["total"]["sites"][s][k] for t in titres) for k in range(3)]
        general["ev_tot"], general["us_tot"], general["st_tot"] = (sum(t["total"]["ev_tot"] for t in titres),
                                                                    sum(t["total"]["us_tot"] for t in titres),
                                                                    sum(t["total"]["st_tot"] for t in titres))
        general["depasse"] = any(t["total"]["depasse"] for t in titres)
    return {"sites": sites, "titres": titres, "general": general}


def _pieds_txt(d: dict) -> str:
    sep = " "
    n = f"{d['n']:,}".replace(",", sep)
    return n if d["auto"] is None else f"{n} / {d['auto']:,}".replace(",", sep)


def bilan_cartes_html(b: dict) -> str:
    """Une carte par titre (repliable s'il y en a plusieurs) : pieds abattus / autorisés, volumes, puis un bandeau par site."""
    def ligne_site(nom, ev, us, st_, cls=""):
        return f'<div class="bc-sl{cls}"><span>{e(nom)}</span><b>{fr(ev)}</b><b>{fr(us)}</b><b>{fr(st_)}</b></div>'

    def essence(l):
        auto = l["auto"]
        pc = min(100, l["n"] / auto * 100) if auto else (100 if l["depasse"] else 0)
        cls = " red" if l["depasse"] else ""
        barre = f'<div class="bc-bar{cls}"><i style="width:{pc:.0f}%"></i></div>' if auto is not None else ""
        pieds = (f'<span class="bc-pieds{cls}"><b>{e(_pieds_txt(l))}</b> pieds{" · dépassé" if l["depasse"] else ""}</span>')
        stats = "".join(f'<div class="bc-st"><span>{lib}</span><b class="{"neg" if (cle == "stock" and l[cle] < -0.0005) else ""}">{fr(l[cle])}</b></div>'
                        for lib, cle in (("Abattu", "abattu"), ("Préparé", "prepare"), ("Exploité", "exploite"), ("Stock forêt", "stock")))
        actifs = [(s, v) for s, v in l["sites"].items() if max(v) > 0.0005]
        if actifs:
            lignes_s = "".join(ligne_site(s, v[0], v[1], v[2]) for s, v in actifs)
            if len(actifs) > 1:
                lignes_s += ligne_site("Total", l["ev_tot"], l["us_tot"], l["st_tot"], " tot")
            sites = ('<div class="bc-sites"><div class="bc-sl hd"><span>Site</span><b>Évacué</b><b>Usiné</b><b>Stock</b></div>'
                     + lignes_s + '</div>')
        else:
            sites = '<div class="bc-aucun">Aucune évacuation</div>'
        return (f'<div class="bc-ess"><div class="bc-l1"><span class="bc-nm"><i style="background:{couleur_essence(l["essence"])}"></i>'
                f'{e(l["essence"])}</span>{pieds}</div>{barre}<div class="bc-stats">{stats}</div>{sites}</div>')

    def entete(titre, d, general=False):
        cls = " red" if d["depasse"] else ""
        sous = f'Abattu {fr(d["abattu"])} · Évacué {fr(d["ev_tot"])} · Usiné {fr(d["us_tot"])}'
        return (f'<div class="bc-h"><div><b>{"Total général" if general else "Titre " + e(titre)}</b><small>{sous}</small></div>'
                f'<span class="bc-pill{cls}">{e(_pieds_txt(d))} pieds</span></div>')

    cartes = []
    if b["general"]:
        g = b["general"]
        cartes.append(f'<div class="bc-card gen">{entete("", g, True)}<div class="bc-pied"><span>Exploité <b>{fr(g["exploite"])}</b></span>'
                      f'<span>Stock forêt <b>{fr(g["stock"])}</b></span></div></div>')
    ouvert = " open" if len(b["titres"]) <= 2 else ""
    for t in b["titres"]:
        corps = "".join(essence(l) for l in t["lignes"])
        pied = (f'<div class="bc-pied"><span>Total titre</span><span>Exploité <b>{fr(t["total"]["exploite"])}</b> · '
                f'Stock forêt <b>{fr(t["total"]["stock"])}</b></span></div>')
        cartes.append(f'<details class="bc-card"{ouvert}><summary>{entete(t["titre"], t["total"])}</summary>{corps}{pied}</details>')
    return '<div class="m4-bt-cartes">' + "".join(cartes) + '</div>'


def bilan_pc_html(b: dict) -> str:
    """Tableau large (PC), même organisation que l'export Excel : colonnes communes, un groupe Évacué/Usiné par site, Stock."""
    sites = b["sites"]
    groupes = list(sites) + (["TOTAL"] if len(sites) > 1 else [])
    h1 = ('<th rowspan="2"></th><th class="r" rowspan="2">Essence</th><th rowspan="2">Pieds<br>abattus / autorisés</th>'
          '<th rowspan="2">Volume abattu</th><th rowspan="2">Préparé</th><th rowspan="2">Exploité</th>'
          + "".join(f'<th colspan="3" class="sg">{e(g)}</th>' for g in groupes) + '<th rowspan="2">Stock forêt</th>')
    h2 = "".join('<th class="sg2">Évacué</th><th class="sg2">Usiné</th><th class="sg2">Stock</th>' for _ in groupes)

    def cells(d):
        cp = "n neg" if d["depasse"] else "n"
        cs = "n neg" if d["stock"] < -0.0005 else "n"
        sit = "".join(f'<td class="n tt">{fr(v[0])}</td><td class="n">{fr(v[1])}</td><td class="n">{fr(v[2])}</td>' for v in d["sites"].values())
        if len(sites) > 1:
            sit += f'<td class="n tt">{fr(d["ev_tot"])}</td><td class="n">{fr(d["us_tot"])}</td><td class="n">{fr(d["st_tot"])}</td>'
        return (f'<td class="{cp}">{e(_pieds_txt(d))}</td><td class="n">{fr(d["abattu"])}</td><td class="n">{fr(d["prepare"])}</td>'
                f'<td class="n">{fr(d["exploite"])}</td>{sit}<td class="{cs}">{fr(d["stock"])}</td>')

    corps = []
    for t in b["titres"]:
        for i, l in enumerate(t["lignes"]):
            prem = f'<td class="tl" rowspan="{len(t["lignes"]) + 1}"><span>{e(t["titre"])}</span></td>' if i == 0 else ""
            corps.append(f'<tr>{prem}<td class="r">{e(l["essence"])}</td>{cells(l)}</tr>')
        corps.append(f'<tr class="t"><td class="r">Total</td>{cells(t["total"])}</tr>')
    if b["general"]:
        corps.append(f'<tr class="g"><td class="tl" style="background:var(--deep)"></td><td class="r">TOTAL</td>{cells(b["general"])}</tr>')
    return (f'<div class="m4-bt-pc"><div class="m4-mx-wrap"><table class="m4-mx m4-bt m4-bt-big"><thead><tr>{h1}</tr><tr>{h2}</tr></thead>'
            f'<tbody>{"".join(corps)}</tbody></table></div></div>')


def bilan_titre_essence_html(df: pd.DataFrame, sites_sel: list | None = None) -> str:
    b = construire_bilan(df, sites_sel)
    if not b["titres"]:
        return ""
    return bilan_cartes_html(b) + bilan_pc_html(b)


def _entetes_bilan(sites: list) -> list[str]:
    cols = ["Titre", "Essence", "Pieds abattus", "Pieds autorisés", "Volume abattu (m³)", "Préparé (m³)", "Exploité (m³)"]
    for s in sites:
        cols += [f"{s} - Évacué (m³)", f"{s} - Usiné (m³)", f"{s} - Stock (m³)"]
    if len(sites) > 1:
        cols += ["TOTAL - Évacué (m³)", "TOTAL - Usiné (m³)", "TOTAL - Stock (m³)"]
    return cols + ["Stock forêt (m³)"]


def _ligne_bilan(titre, essence, d, sites) -> list:
    v = [titre, essence, d["n"], d["auto"] if d["auto"] is not None else "", d["abattu"], d["prepare"], d["exploite"]]
    for s in sites:
        v += [d["sites"][s][0], d["sites"][s][1], d["sites"][s][2]]
    if len(sites) > 1:
        v += [d["ev_tot"], d["us_tot"], d["st_tot"]]
    return v + [d["stock"]]


def bilan_titre_essence_csv(df: pd.DataFrame, sites_sel: list | None = None) -> bytes:
    """Même structure que l'Excel, à plat (séparateur « ; », virgule décimale, ouvert directement par Excel)."""
    b = construire_bilan(df, sites_sel)
    lignes = []
    for t in b["titres"]:
        lignes += [_ligne_bilan(t["titre"], l["essence"], l, b["sites"]) for l in t["lignes"]]
        lignes.append(_ligne_bilan(t["titre"], "Total", t["total"], b["sites"]))
    if b["general"]:
        lignes.append(_ligne_bilan("TOTAL", "", b["general"], b["sites"]))
    return (pd.DataFrame(lignes, columns=_entetes_bilan(b["sites"])).round(3)
            .to_csv(index=False, sep=";", decimal=",", float_format="%.3f").encode("utf-8-sig"))


def bilan_titre_essence_xlsx(df: pd.DataFrame, sites_sel: list | None = None, filtres_txt: str = "") -> bytes:
    """Classeur Excel mis en page : colonne Titre fusionnée (texte vertical), un groupe Évacué/Usiné par site, Stock, totaux."""
    from openpyxl import Workbook
    from openpyxl.styles import Alignment, Border, Font, PatternFill, Side
    from openpyxl.utils import get_column_letter as lettre
    from openpyxl.worksheet.properties import PageSetupProperties
    b = construire_bilan(df, sites_sel)
    sites = b["sites"]
    groupes = list(sites) + (["TOTAL"] if len(sites) > 1 else [])
    wb = Workbook()
    ws = wb.active
    ws.title = "Bilan"
    vert, vert2, clair, gris = "1B4332", "40916C", "D8EFE0", "F3F7F4"
    fine = Side(style="thin", color="B9C7BC")
    bord = Border(left=fine, right=fine, top=fine, bottom=fine)
    ncol = 7 + 3 * len(groupes) + 1
    ws.merge_cells(start_row=1, start_column=1, end_row=1, end_column=ncol)
    ws["A1"] = "Bilan par titre et par essence (m³)"
    ws["A1"].font = Font(name="Calibri", size=14, bold=True, color=vert)
    ws.merge_cells(start_row=2, start_column=1, end_row=2, end_column=ncol)
    ws["A2"] = f"Édité le {datetime.now(FUSEAU):%d/%m/%Y à %H:%M}" + (f" · {filtres_txt}" if filtres_txt else "")
    ws["A2"].font = Font(name="Calibri", size=9, italic=True, color="5A6F60")
    fixes = ["Titre", "Essence", "Pieds abattus", "Pieds autorisés", "Volume abattu", "Préparé", "Exploité"]
    for i, h in enumerate(fixes, 1):
        ws.merge_cells(start_row=4, start_column=i, end_row=5, end_column=i)
        ws.cell(4, i, h)
    c = 8
    for g in groupes:
        ws.merge_cells(start_row=4, start_column=c, end_row=4, end_column=c + 2)
        ws.cell(4, c, g)
        ws.cell(5, c, "Évacué")
        ws.cell(5, c + 1, "Usiné")
        ws.cell(5, c + 2, "Stock")
        c += 3
    ws.merge_cells(start_row=4, start_column=c, end_row=5, end_column=c)
    ws.cell(4, c, "Stock forêt")
    for r in (4, 5):
        for k in range(1, ncol + 1):
            cel = ws.cell(r, k)
            groupe_site = 8 <= k < ncol
            cel.fill = PatternFill("solid", fgColor=(vert2 if groupe_site else vert))
            cel.font = Font(name="Calibri", size=10, bold=True, color="FFFFFF")
            cel.alignment = Alignment(horizontal="center", vertical="center", wrap_text=True)
            cel.border = bord
    ws.row_dimensions[4].height = 22
    ws.row_dimensions[5].height = 18
    ligne = 6

    def ecrire(r, titre, nom, d, style):
        vals = _ligne_bilan(titre, nom, d, sites)
        for k, v in enumerate(vals, 1):
            cel = ws.cell(r, k, None if (k == 1 and style != "g") else v)
            cel.border = bord
            cel.font = Font(name="Calibri", size=10, bold=style in ("t", "g"), color="FFFFFF" if style == "g" else "000000")
            if style == "t":
                cel.fill = PatternFill("solid", fgColor=clair)
            elif style == "g":
                cel.fill = PatternFill("solid", fgColor=vert)
            if k >= 3:
                cel.alignment = Alignment(horizontal="right")
                cel.number_format = "0" if k in (3, 4) else "#,##0.000"
        if d["depasse"]:
            ws.cell(r, 3).font = Font(name="Calibri", size=10, bold=True, color="FFB4AE" if style == "g" else "B94A44")
        if d["stock"] < -0.0005:
            ws.cell(r, ncol).font = Font(name="Calibri", size=10, bold=True, color="FFB4AE" if style == "g" else "B94A44")

    for t in b["titres"]:
        debut = ligne
        for l in t["lignes"]:
            ecrire(ligne, t["titre"], l["essence"], l, "n")
            ligne += 1
        ecrire(ligne, t["titre"], "Total", t["total"], "t")
        ligne += 1
        ws.merge_cells(start_row=debut, start_column=1, end_row=ligne - 1, end_column=1)
        cel = ws.cell(debut, 1, t["titre"])
        cel.alignment = Alignment(horizontal="center", vertical="center", text_rotation=90)
        cel.font = Font(name="Calibri", size=11, bold=True, color="FFFFFF")
        for rr in range(debut, ligne):
            ws.cell(rr, 1).fill = PatternFill("solid", fgColor=vert2)
            ws.cell(rr, 1).border = bord
    if b["general"]:
        ecrire(ligne, "TOTAL", "", b["general"], "g")
        ws.cell(ligne, 1).value = "TOTAL"
        ws.cell(ligne, 1).alignment = Alignment(horizontal="center")
    ws.column_dimensions["A"].width = 8
    ws.column_dimensions["B"].width = 14
    for k in range(3, ncol + 1):
        ws.column_dimensions[lettre(k)].width = 13
    ws.freeze_panes = "C6"
    ws.sheet_view.showGridLines = False
    ws.page_setup.orientation = "landscape"
    ws.page_setup.fitToWidth = 1
    ws.page_setup.fitToHeight = 0
    ws.sheet_properties.pageSetUpPr = PageSetupProperties(fitToPage=True)
    ws.print_title_rows = "4:5"
    sortie = io.BytesIO()
    wb.save(sortie)
    return sortie.getvalue()


# ----- Vue 1 : Aperçu --------------------------------------------------------
def volumes_sites(df: pd.DataFrame, sites: list) -> tuple[float, float, float]:
    """Évacué, usiné et stock du parc de rupture des sites choisis, pour les (essence, titre) du filtre."""
    par_site = charger_bilan_sites()
    cles = set(zip(df["essence"], df["titre"]))
    voulus = {s.upper() for s in sites}
    ev = us = st_ = 0.0
    for cle in cles:
        for s, v in par_site.get(cle, {}).items():
            if s in voulus:
                ev, us, st_ = ev + v[0], us + v[1], st_ + v[2]
    return ev, us, st_


def vue_apercu(df: pd.DataFrame, ev: pd.DataFrame, titre: list, essence: list):
    sites = sites_filtres()
    filtres_actifs(titre, essence, sites)
    d = totaux(df)
    nb_lv = int(ev["lv"].nunique()) if len(ev) and not sites else 0
    stock_site = None
    if sites:     # le site ne touche que ce qui est rattaché aux billes évacuées : évacué, usiné et stock du parc de ces sites
        d["evacue"], d["usine"], stock_site = volumes_sites(df, sites)
        d["taux_evac"] = (d["evacue"] / d["billonne"] * 100) if d["billonne"] > 0 else 0.0
    st.markdown('<div class="m4-kpis">'
                + kpi("Abattu", fr(d["abattu"]), couleur="#2D6A4F", sous=f"{int(d['n_abattu'])} grume(s) · {nb_df10(titre, essence)} DF10")
                + kpi("Exploité", fr(d["billonne"]), couleur="#52B788", sous=f"{int(d['n_billes'])} bille(s)")
                + kpi("Perte billonnage", f"{d['perte']:+.3f}".replace(".", ","), couleur="#B94A44",
                      sous=f"{d['perte_pct']:.1f} % des grumes billonnées")
                + kpi("Évacué", fr(d["evacue"]), couleur="#C9A27A",
                      sous=f"taux {d['taux_evac']:.1f} %" + (f" · {nb_lv} LV" if nb_lv else "") + (" · site(s) choisi(s)" if sites else ""))
                + kpi("Usiné", fr(d["usine"]), couleur="#7A4E2D")
                + (kpi("Stock du site", fr(stock_site), couleur="#2D6A4F", sous="au parc de rupture") if sites else "")
                + kpi("Abandon", fr(d["abandon"]), couleur="#8A8A6A")
                + '</div>', unsafe_allow_html=True)
    par_ess = sorted(agreger(df, "essence"), key=lambda x: x[1]["billonne"], reverse=True)
    par_ess = [(n, x) for n, x in par_ess if x["billonne"] > 0]
    st.markdown('<div class="m4-sec">Répartition de l’exploité par essence</div>', unsafe_allow_html=True)
    if not par_ess or d["billonne"] <= 0:
        st.markdown('<div class="m4-vide">Aucune donnée pour ces filtres.</div>', unsafe_allow_html=True)
        return
    total = d["billonne"]
    visibles, autres = par_ess[:6], par_ess[6:]
    segments = [(n or "Autre", x["billonne"], couleur_essence(n)) for n, x in visibles]
    if autres:
        segments.append((f"Autres ({len(autres)})", sum(x["billonne"] for _, x in autres), "#B9C7BC"))
    barre = "".join(f'<i style="width:{v / total * 100:.2f}%;background:{c}" title="{e(n)}"></i>' for n, v, c in segments)
    legende = "".join(f'<span><i class="m4-dot" style="background:{c}"></i>{e(n)} <b>{v / total * 100:.1f} %</b></span>'
                      for n, v, c in segments)
    st.markdown(f'<div class="m4-stack">{barre}</div><div class="m4-legend">{legende}</div>', unsafe_allow_html=True)
    tableau = bilan_titre_essence_html(df, sites)
    if tableau:
        st.markdown('<div class="m4-sec">Bilan par titre et par essence (m³)</div>' + tableau, unsafe_allow_html=True)
        st.caption("Pieds = abattus / autorisés par le permis (en rouge : dépassement) · Préparé = billonné, abandon compris · "
                   "Exploité = hors abandon · Stock forêt = exploité − évacué (tous sites) · Stock d'un site = billes actuellement au "
                   "parc de rupture de ce site. Usiné = billes en Parc usine. Évacué et usiné sont ventilés par site d'après le site enregistré sur chaque bille."
                   + (" Le filtre Site limite l'évacué, l'usiné et le stock du site." if sites else "")
                   + " Touchez un titre pour ouvrir ou replier sa carte.")
        txt_f = " · ".join(x for x in (("Titre : " + ", ".join(titre)) if titre else "", ("Sites : " + ", ".join(sites)) if sites else "",
                                       ("Essence : " + ", ".join(essence)) if essence else "") if x)
        st.download_button("Télécharger le bilan (Excel)", bilan_titre_essence_xlsx(df, sites, txt_f), file_name="bilan_titre_essence.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", width="stretch",
                           icon=":material/download:", key="dl_bilan_te_x", type="primary")
        st.download_button("Télécharger le bilan (CSV)", bilan_titre_essence_csv(df, sites), file_name="bilan_titre_essence.csv",
                           mime="text/csv", width="stretch", icon=":material/table_view:", key="dl_bilan_te")
    st.markdown('<div class="m4-sec">Rapports détaillés</div>', unsafe_allow_html=True)
    st.caption("Ouvrez l'onglet « Rapports » : par essence, par titre, croisé essence × titre, et le rapport d'évacuation (LV utilisés).")


# ----- Vue 2 : Rapports ------------------------------------------------------
TRI = {"Exploité": "billonne", "Abattu": "abattu", "Évacué": "evacue", "Usiné": "usine", "Perte": "perte", "A–Z": "nom"}
MODES_RAPPORT = ["Synthèse", "Évacuation"]
MODE_CHANTIER = "Rapport de chantier"   # rapport Word complet d'un titre (Traçabilité, Administration)


def vue_rapports(df: pd.DataFrame, ev: pd.DataFrame, titre: list, essence: list):
    filtres_actifs(titre, essence)
    if df.empty:
        st.markdown('<div class="m4-vide">Aucune donnée pour ces filtres.</div>', unsafe_allow_html=True)
        return
    modes = MODES_RAPPORT + ([MODE_CHANTIER] if role_actuel() in ("tracabilite", "administration") else [])
    st.html("<style>.st-key-rap_mode button{ min-width:0 !important; padding-left:.3rem !important; padding-right:.3rem !important; }"
            ".st-key-rap_mode button p{ white-space:normal !important; overflow:visible !important; text-overflow:clip !important;"
            " text-align:center; line-height:1.15 !important; }</style>")
    mode = seg("Rapport", modes, default="Synthèse", key="rap_mode",
                                label_visibility="collapsed") or "Synthèse"
    if mode == "Évacuation":
        return rapport_evacuation(ev)
    if mode == MODE_CHANTIER:
        return rapport_fin_chantier()

    regroupe = seg("Regrouper par", ["Essence", "Titre"], default="Essence", key="rap_par",
                   label_visibility="collapsed") or "Essence"
    par = "essence" if regroupe == "Essence" else "titre"
    autre = "titre" if par == "essence" else "essence"
    filtre = ""   # le filtrage par titre / essence se fait une seule fois, en haut de page
    tri = seg("Trier par", list(TRI), default="Exploité", key="rap_tri",
                               label_visibility="collapsed") or "Exploité"
    cle_tri = TRI[tri]
    lignes = agreger(df, par)
    if filtre.strip():
        lignes = [(n, d) for n, d in lignes if filtre.strip().lower() in (n or "").lower()]
    if cle_tri == "nom":
        lignes.sort(key=lambda x: (x[0] or "~").lower())
    else:
        lignes.sort(key=lambda x: x[1][cle_tri], reverse=True)
    vide = "Non renseignée" if par == "essence" else "Sans titre"
    lignes = [(n or vide, d) for n, d in lignes]
    if not lignes:
        st.markdown('<div class="m4-vide">Aucun résultat.</div>', unsafe_allow_html=True)
        return

    lv_par = ev.groupby(par)["lv"].nunique().to_dict() if len(ev) else {}
    ev_sel = ev if not filtre.strip() else ev[ev[par].str.contains(filtre.strip(), case=False, regex=False)]
    df_sel = df if not filtre.strip() else df[df[par].str.contains(filtre.strip(), case=False, regex=False)]
    mesure = "billonne" if cle_tri == "nom" else cle_tri
    st.markdown(carte_total(totaux(df_sel), f"{len(lignes)} {'essence(s)' if par == 'essence' else 'titre(s)'}",
                            actif=mesure, nb_lv=int(ev_sel["lv"].nunique()) if len(ev_sel) else 0), unsafe_allow_html=True)
    cartes = []
    for rang, (nom, d) in enumerate(lignes[:MAX_CARTES], start=1):
        brut = "" if nom == vide else nom
        sous = df[df[par] == brut]
        detail = sorted(agreger(sous, autre), key=lambda x: x[1]["billonne"], reverse=True)
        detail = [((n or ("Sans titre" if autre == "titre" else "Non renseignée")), x) for n, x in detail]
        couleur = couleur_essence(brut) if par == "essence" else "#2D6A4F"
        cd = (lambda n: couleur_essence("" if n == "Non renseignée" else n)) if autre == "essence" else (lambda n: "#2D6A4F")
        cartes.append(carte_rapport(nom, d, couleur,
                                    "Ventilation par titre" if par == "essence" else "Ventilation par essence", detail, cd,
                                    mesure=mesure, rang=None if cle_tri == "nom" else rang, nb_lv=lv_par.get(brut, 0)))
    st.markdown("".join(cartes), unsafe_allow_html=True)
    if len(lignes) > MAX_CARTES:
        st.info(f"{len(lignes)} lignes — les {MAX_CARTES} premières sont affichées. Utilisez le filtre.")
    def _ligne_export(nom, d):
        return {"Essence" if par == "essence" else "Titre": nom, "Abattu (m³)": d["abattu"],
                "Exploité (m³)": d["billonne"], "Abandon (m³)": d["abandon"], "Perte (m³)": d["perte"],
                "Évacué (m³)": d["evacue"], "Usiné (m³)": d["usine"]}
    export = pd.DataFrame([_ligne_export(n, d) for n, d in lignes] + [_ligne_export("TOTAL", totaux(df_sel))])
    telecharger(export, f"rapport_{par}.csv", f"dl_{par}")


# ----- Rapport de fin de chantier (Word) : un titre, de la date de début à la date d'arrêt ----------------
def donnees_chantier(titre: str, debut, arret) -> dict:
    """Rassemble les flux d'un titre pour rapport_chantier.construire()."""
    nom = lambda x: (x or "").strip().upper()
    # abattage (dates vides = comptées ; elles ne peuvent pas être situées)
    ab = {nom(r["e"]): (int(r["n"]), float(r["v"])) for r in requete(
        "SELECT UPPER(TRIM(essence)) AS e, COUNT(*) AS n, COALESCE(SUM(volume),0) AS v FROM abattage "
        "WHERE TRIM(titre) = %s AND (date IS NULL OR (date >= %s AND date <= %s)) GROUP BY 1", (titre, debut, arret))}
    carnets = [(int(r["c"]), float(r["v"])) for r in requete(
        "SELECT split_part(TRIM(df10), '/', 1) AS c, COALESCE(SUM(volume),0) AS v FROM abattage "
        "WHERE TRIM(titre) = %s AND (date IS NULL OR (date >= %s AND date <= %s)) AND TRIM(COALESCE(df10,'')) <> '' "
        "AND split_part(TRIM(df10), '/', 1) ~ '^[0-9]+$' GROUP BY 1", (titre, debut, arret))]
    # Préparé = tout ce qui a été billonné (abandon compris) ; Exploité = billonné hors abandon
    prep = requete(
        f"SELECT UPPER(TRIM(essence)) AS e, (date_billonnage < %s) AS avant, COUNT(*) AS n, COALESCE(SUM(volume),0) AS v, "
        f"COUNT(*) FILTER (WHERE {NON_ABANDON}) AS n_exp, COALESCE(SUM(volume) FILTER (WHERE {NON_ABANDON}),0) AS v_exp "
        f"FROM billonnage b WHERE TRIM(titre) = %s AND (date_billonnage IS NULL OR date_billonnage <= %s) GROUP BY 1, 2",
        (debut, titre, arret))
    # colonne SITE (Batouri / Sengbot) : présente une fois la base du PC mise à jour et synchronisée
    a_site = bool(requete("SELECT 1 FROM information_schema.columns WHERE table_schema = 'public' "
                          "AND table_name = 'billonnage' AND column_name = 'site'"))
    expr_site = "UPPER(TRIM(COALESCE(site,'')))" if a_site else "''"
    evac = requete(
        "SELECT UPPER(TRIM(essence)) AS e, UPPER(TRIM(COALESCE(situation,''))) AS s, (date_evacuation < %s) AS avant, "
        f"{expr_site} AS site, COUNT(*) AS n, COALESCE(SUM(volume),0) AS v FROM billonnage b WHERE TRIM(titre) = %s AND {NON_ABANDON} "
        "AND UPPER(TRIM(COALESCE(situation,''))) = ANY(%s) AND (date_evacuation IS NULL OR date_evacuation <= %s) GROUP BY 1, 2, 3, 4",
        (debut, titre, SITUATIONS_EVACUEES, arret))
    preparation, exploitation, stock0 = {}, {}, {}
    for r in prep:
        e = nom(r["e"])
        if r["avant"]:
            stock0[e] = stock0.get(e, 0.0) + float(r["v_exp"])      # le stock ne compte que l'exploité
        else:
            n, v = preparation.get(e, (0, 0.0))
            preparation[e] = (n + int(r["n"]), v + float(r["v"]))
            n, v = exploitation.get(e, (0, 0.0))
            exploitation[e] = (n + int(r["n_exp"]), v + float(r["v_exp"]))
    dest: dict[tuple, dict] = {}
    for r in evac:
        e = nom(r["e"])
        if r["avant"]:
            stock0[e] = stock0.get(e, 0.0) - float(r["v"])
            continue
        s = r["s"]
        genre = "USINE" if "USINE" in s else "RUPTURE" if "RUPTURE" in s else "NEGOCE"
        m = dest.setdefault((genre, (r["site"] or "") if genre != "NEGOCE" else ""), {})
        n, v = m.get(e, (0, 0.0))
        m[e] = (n + int(r["n"]), v + float(r["v"]))

    def libelle(genre, site):
        base = {"USINE": "parc Usine", "RUPTURE": "parc de Rupture", "NEGOCE": "négoce"}[genre]
        if genre == "NEGOCE":
            return base
        if site:
            return f"{base} de {site.capitalize()}"
        return base + (" (site non précisé)" if a_site else "")
    ordre_genre = {"USINE": 0, "RUPTURE": 1, "NEGOCE": 2}
    evacuations = [(libelle(g, si), {e: x for e, x in m.items() if abs(x[1]) > 0.0005})
                   for (g, si), m in sorted(dest.items(), key=lambda kv: (ordre_genre[kv[0][0]], kv[0][1] == "", kv[0][1]))]
    evacuations = [x for x in evacuations if x[1]]
    nonnul = lambda m: {e: x for e, x in m.items() if abs(x[1]) > 0.0005}
    return {"titre": titre, "societe": "S.T.B.K", "exercice": str(arret.year), "debut": debut, "arret": arret,
            "carnets": carnets, "abattage": nonnul(ab), "preparation": nonnul(preparation), "exploitation": nonnul(exploitation), "evacuations": evacuations,
            "stock_initial": stock0}


def rapport_fin_chantier():
    st.markdown("Rapport d'activités **Word** d'un titre, sur le modèle du rapport de fin de chantier : documents DF10, "
                "abattage, préparation, évacuations par destination et synthèse avec stocks.")
    try:
        titres = listes_filtres()[0]
    except Exception:
        titres = []
    if not titres:
        st.markdown('<div class="m4-vide">Aucun titre disponible.</div>', unsafe_allow_html=True)
        return
    deja = [t for t in (st.session_state.get("ft") or []) if t in titres]
    titre = st.selectbox("Titre", titres, index=titres.index(deja[0]) if len(deja) == 1 else 0, key="rc_titre")
    # Période par défaut = activité réelle du titre : début = abattage le plus ancien ;
    # fin = date la plus récente parmi abattage, billonnage et évacuation.
    d0 = requete(
        "SELECT (SELECT MIN(date) FROM abattage WHERE TRIM(titre) = %s) AS debut, "
        "GREATEST((SELECT MAX(date) FROM abattage WHERE TRIM(titre) = %s), "
        f"(SELECT MAX(b.date_billonnage) FROM billonnage b WHERE TRIM(b.titre) = %s), "
        f"(SELECT MAX({DATE_EVAC}) FROM billonnage b WHERE TRIM(b.titre) = %s)) AS fin",
        (titre, titre, titre, titre))
    aujourdhui = datetime.now(FUSEAU).date()
    debut_def = (d0[0]["debut"] if d0 and d0[0]["debut"] else date(aujourdhui.year, 1, 1))
    arret_def = (d0[0]["fin"] if d0 and d0[0]["fin"] else aujourdhui)
    c1, c2 = st.columns(2)
    debut = c1.date_input("Début", value=debut_def, key=f"rc_debut_{titre}", format="DD/MM/YYYY")
    arret = c2.date_input("Arrêt (inclus)", value=arret_def, key=f"rc_arret_{titre}", format="DD/MM/YYYY")
    st.caption(f"Par défaut : du premier abattage ({debut_def:%d/%m/%Y}) à l'activité la plus récente "
               f"({arret_def:%d/%m/%Y} : abattage, billonnage ou évacuation).")
    if arret < debut:
        st.error("La date d'arrêt doit suivre la date de début.")
        return
    with st.spinner("Calcul des flux…"):
        d = donnees_chantier(titre, debut, arret)
    if not d["abattage"] and not d["preparation"]:
        st.markdown('<div class="m4-vide">Aucune donnée pour ce titre sur cette période.</div>', unsafe_allow_html=True)
        return
    ta = sum(x[1] for x in d["abattage"].values())
    tp = sum(x[1] for x in d["preparation"].values())
    tx = sum(x[1] for x in d["exploitation"].values())
    te = sum(x[1] for m in d["evacuations"] for x in m[1].values())
    st.markdown('<div class="m4-kpis three">' + kpi("Abattu", fr(ta), "m³", "#2D6A4F") + kpi("Préparé", fr(tp), "m³", "#52B788")
                + kpi("Exploité", fr(tx), "m³", "#40916C")
                + kpi("Évacué", fr(te), "m³", "#B5651D") + kpi("Stock", fr(sum(d["stock_initial"].values()) + tx - te), "m³", "#6C8EAD")
                + '</div>', unsafe_allow_html=True)
    st.caption(f"{len(d['carnets'])} feuillet(s) DF10 · {len(d['evacuations'])} destination(s) d'évacuation. "
               "Préparé = volume billonné (abandon compris) ; Exploité = hors abandon ; le stock part de l’exploité.")
    octets = rapport_chantier.construire(d)
    nom = f"Rapport_{_slug(titre)}_{arret:%Y%m%d}.docx"
    st.download_button("Télécharger le rapport (Word)", octets, file_name=nom,
                       mime="application/vnd.openxmlformats-officedocument.wordprocessingml.document",
                       type="primary", width="stretch", icon=":material/description:", key="rc_dl",
                       on_click=noter, args=(st.session_state["utilisateur"]["id"], "rapport", f"Fin de chantier {titre}"))


# ----- Rapport d'évacuation : volumes, billes, LV, camions -------------------
MOIS_FR = ["janvier", "février", "mars", "avril", "mai", "juin", "juillet", "août", "septembre", "octobre",
           "novembre", "décembre"]
TRI_EVAC = {"Volume": "volume", "LV": "lv", "Billes": "billes", "A–Z": "nom"}


def _nom_groupe(cle: str, par: str) -> str:
    if par == "Mois" and re.fullmatch(r"\d{4}-\d{2}", cle):
        return f"{MOIS_FR[int(cle[5:]) - 1].capitalize()} {cle[:4]}"
    if par == "Jour" and re.fullmatch(r"\d{4}-\d{2}-\d{2}", cle):
        return f"{cle[8:]}/{cle[5:7]}/{cle[:4]}"
    return cle


def carte_evac(nom: str, s: dict, g: pd.DataFrame, sous_par: str, couleur: str, vmax: float, rang: int | None) -> str:
    """Carte dépliable d'un groupe d'évacuations : volume, LV, billes, camions ; au toucher : ventilation + liste des LV."""
    vide = "Sans titre" if sous_par == "titre" else "Non renseignée"
    sous = []
    for cle, h in g.groupby(sous_par, sort=False):
        sous.append(((cle or vide), float(h["volume"].sum()), len(h), int(h["lv"].nunique())))
    sous.sort(key=lambda x: -x[1])
    smax = max((x[1] for x in sous), default=0.0)
    lignes = []
    for n, v, nb, lv in sous:
        coul = couleur_essence("" if n == vide else n) if sous_par == "essence" else "#2D6A4F"
        pct = max(2.0, v / smax * 100) if smax > 0 else 0
        lignes.append(f'<div class="m4-sub"><div class="m4-sub-top"><span class="m4-dot" style="background:{coul}"></span>'
                      f'<b>{e(n)}</b><span class="v">{fr(v)} <small style="font-weight:500;color:#5A6F60">m³</small></span></div>'
                      f'<div class="m4-gauge"><i style="width:{pct:.0f}%;background:{coul}"></i></div>'
                      f'<div class="m4-ess-sub">{nb} bille(s) · {lv} LV</div></div>')
    lvs = sorted({x for x in g["lv"].dropna()}, key=cle_naturelle)
    puces = "".join(f"<span>{e(x)}</span>" for x in lvs)
    bloc_lv = (f'<div class="m4-body-h" style="margin-top:.7rem">N° LV utilisés ({len(lvs)})</div>'
               f'<div class="m4-lvs">{puces}</div>') if lvs else ""
    pct = max(2.0, s["volume"] / vmax * 100) if vmax > 0 else 0
    rg = f'<span class="m4-rank">{rang}</span>' if rang else ""
    chips = (f'<span class="m4-c wood">{s["lv"]} LV</span><span class="m4-c ok">{s["billes"]} bille(s)</span>'
             f'<span class="m4-c ok">{s["camions"]} camion(s)</span>')
    return (f'<details class="m4-card"><summary><div class="m4-card-top">{rg}<span class="m4-dot" style="background:{couleur}"></span>'
            f'<b>{e(nom)}</b><span class="m4-card-vol">{fr(s["volume"])} <small>m³ évacué</small></span>'
            f'<span class="m4-chev"></span></div><div class="m4-gauge2"><i style="width:{pct:.0f}%;background:{couleur}"></i></div>'
            f'<div class="m4-chips">{chips}</div></summary>'
            f'<div class="m4-body"><div class="m4-body-h">Ventilation par {"titre" if sous_par == "titre" else "essence"}</div>'
            f'{"".join(lignes)}{bloc_lv}</div></details>')


def rapport_evacuation(ev: pd.DataFrame):
    """Évacuations sur une période : volume, nombre de billes, de LV et de camions, groupés au choix."""
    if ev.empty:
        st.markdown('<div class="m4-vide">Aucune évacuation pour ces filtres.</div>', unsafe_allow_html=True)
        return
    du, au = choix_periode("ev")
    par = seg("Regrouper par", ["Essence", "Titre", "Mois", "Jour"], default="Essence", key="ev_par",
                               label_visibility="collapsed") or "Essence"
    d = ev
    if du:
        d = d[d["date"] >= pd.Timestamp(du)]
    if au:
        d = d[d["date"] <= pd.Timestamp(au)]
    if d.empty:
        st.markdown(f'<div class="m4-vide">Aucune évacuation {e(texte_periode(du, au))}.</div>', unsafe_allow_html=True)
        return
    s = stats_evac(d)
    if du or au:
        periode = texte_periode(du, au)
    elif pd.notna(s["du"]):
        periode = f"{s['du']:%d/%m/%Y} → {s['au']:%d/%m/%Y}"
    else:
        periode = "toute la période"
    note = (f'<div class="m4-note">{s["sans_lv"]} bille(s) évacuée(s) sans N° LV renseigné.</div>' if s["sans_lv"] else "")
    st.markdown(f'<div class="m4-total"><div class="m4-total-h"><b>Évacuation</b><span>{e(periode)}</span></div>'
                f'<div class="m4-evk"><div><b>{fr(s["volume"])}</b><span>m³ évacués</span></div>'
                f'<div><b>{s["lv"]}</b><span>LV utilisés</span></div>'
                f'<div><b>{s["billes"]}</b><span>billes</span></div>'
                f'<div><b>{s["camions"]}</b><span>camions</span></div></div>{note}</div>', unsafe_allow_html=True)

    if par == "Essence":
        cle = d["essence"].replace("", "Non renseignée")
    elif par == "Titre":
        cle = d["titre"].replace("", "Sans titre")
    elif par == "Mois":
        cle = d["date"].dt.strftime("%Y-%m")
    else:
        cle = d["date"].dt.strftime("%Y-%m-%d")
    d = d.assign(cle=cle.fillna("Date inconnue"))
    sous_par = "titre" if par == "Essence" else "essence"
    groupes = [(k, stats_evac(g), g) for k, g in d.groupby("cle", sort=False)]
    groupes = [x for x in groupes if abs(x[1]["volume"]) > 0.0005]   # pas de ligne à 0,000 m³
    chrono = par in ("Mois", "Jour")
    par_nom = False
    if chrono:   # plus récent d'abord, « Date inconnue » en dernier
        connus = sorted([x for x in groupes if x[0] != "Date inconnue"], key=lambda x: x[0], reverse=True)
        groupes = connus + [x for x in groupes if x[0] == "Date inconnue"]
    else:
        tri = seg("Trier par", list(TRI_EVAC), default="Volume", key="ev_tri",
                                   label_visibility="collapsed") or "Volume"
        par_nom = TRI_EVAC[tri] == "nom"
        if par_nom:
            groupes.sort(key=lambda x: x[0].lower())
        else:
            groupes.sort(key=lambda x: x[1][TRI_EVAC[tri]], reverse=True)
    vmax = max((x[1]["volume"] for x in groupes), default=0.0)
    cartes = []
    for rang, (k, sg, g) in enumerate(groupes[:MAX_CARTES], start=1):
        couleur = couleur_essence("" if k == "Non renseignée" else k) if par == "Essence" else "#2D6A4F"
        cartes.append(carte_evac(_nom_groupe(k, par), sg, g, sous_par, couleur, vmax,
                                 None if (chrono or par_nom) else rang))
    st.markdown("".join(cartes), unsafe_allow_html=True)
    if len(groupes) > MAX_CARTES:
        st.info(f"{len(groupes)} lignes — les {MAX_CARTES} premières sont affichées.")
    tot = stats_evac(d)
    export = pd.DataFrame([{par: _nom_groupe(k, par), "Volume évacué (m³)": sg["volume"], "Billes": sg["billes"],
                            "LV utilisés": sg["lv"], "Camions": sg["camions"]} for k, sg, g in groupes]
                          + [{par: "TOTAL", "Volume évacué (m³)": tot["volume"], "Billes": tot["billes"],
                              "LV utilisés": tot["lv"], "Camions": tot["camions"]}])
    telecharger(export, f"evacuation_par_{par.lower()}.csv", "dl_evac")


# ----- Vue 3 : Rechercher ----------------------------------------------------
MODE_AUTO = "Numéros"
MODE_CRIT = "Critères"
MAX_LIGNES_CRITERES = 500000   # simple garde-fou : en pratique, toutes les billes sont listées et exportées
ETATS = ["Toutes", "Évacuées", "En stock", "Usinées", "Abandon"]
SIT_STOCK = "UPPER(b.situation) LIKE '%%PARC DE RUPTURE%%'"
OK_STATUT, KO_STATUT = "✅", "❌"


def icone_statut(v) -> str:
    """Statut affiché en icône : croix rouge si Abandon, coche verte sinon."""
    return KO_STATUT if str(v or "").strip().upper() == "ABANDON" else OK_STATUT


def _echapper_like(t: str) -> str:
    return t.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")


def _jetons(texte: str) -> list[str]:
    return [t for t in re.split(r"[\s,;]+", (texte or "").strip()) if t]


def conditions_criteres(f: dict) -> tuple[str, list]:
    """WHERE + paramètres de la recherche multicritères (tous les critères renseignés s'additionnent)."""
    w, p = [], []
    if f["essences"]:
        w.append("UPPER(TRIM(b.essence)) = ANY(%s)")
        p.append(f["essences"])
    if f["titres"]:
        w.append("TRIM(b.titre) = ANY(%s)")
        p.append(f["titres"])
    if f["etat"] == "Évacuées":
        w.append(f"{SIT_EVAC} AND {NON_ABANDON}")
        p.append(SITUATIONS_EVACUEES)
    elif f["etat"] == "En stock":
        w.append(f"{SIT_STOCK} AND {NON_ABANDON}")
    elif f["etat"] == "Usinées":
        w.append("UPPER(TRIM(COALESCE(b.situation,''))) = 'PARC USINE' AND UPPER(TRIM(COALESCE(b.statut,''))) <> 'ABANDON'")
    elif f["etat"] == "Abandon":
        w.append("UPPER(TRIM(COALESCE(b.statut,''))) = 'ABANDON'")
    if f["du"]:
        w.append(f"{DATE_EVAC} >= %s")
        p.append(f["du"])
    if f["au"]:
        w.append(f"{DATE_EVAC} <= %s")
        p.append(f["au"])
    if f["lv"]:
        w.append("(UPPER(TRIM(b.numero_lv)) = ANY(%s) OR UPPER(TRIM(b.code_barre_lv)) = ANY(%s))")
        p += [[x.upper() for x in f["lv"]]] * 2
    if f.get("sites"):
        w.append("UPPER(TRIM(COALESCE(b.site,''))) = ANY(%s)")
        p.append([x.upper() for x in f["sites"]])
    if f["situations"]:
        w.append("UPPER(TRIM(b.situation)) = ANY(%s)")
        p.append([x.upper() for x in f["situations"]])
    if f["sequences"]:
        w.append("TRIM(b.sequence) LIKE ANY(%s)")
        p.append(["%" + _echapper_like(x) for x in f["sequences"]])
    if f["df10"]:
        w.append("TRIM(b.df10) LIKE ANY(%s)")
        p.append([_echapper_like(x) + "%" for x in f["df10"]])
    return (" AND ".join(w) or "TRUE"), p


def resume_criteres(f: dict) -> str:
    parts = []
    if f["essences"]:
        parts.append(", ".join(f["essences"]))
    if f["titres"]:
        parts.append("titre " + ", ".join(f["titres"]))
    if f["etat"] != "Toutes":
        parts.append(f["etat"].lower())
    if f["du"] or f["au"]:
        parts.append("évacuation " + texte_periode(f["du"], f["au"]))
    if f["lv"]:
        parts.append("LV " + ", ".join(f["lv"]))
    if f.get("sites"):
        parts.append("site " + ", ".join(f["sites"]))
    if f["situations"]:
        parts.append("situation " + ", ".join(f["situations"]))
    if f["sequences"]:
        parts.append("séquence(s) finissant par " + ", ".join(f["sequences"]))
    if f["df10"]:
        parts.append("DF10 commençant par " + ", ".join(f["df10"]))
    return " · ".join(parts)


def csv_billes(df: pd.DataFrame) -> bytes:
    """Export des billes : volumes à 3 décimales, longueurs à 1 décimale, dates JJ/MM/AAAA."""
    x = df.copy()
    x["Vol. (m³)"] = x["Vol. (m³)"].map(lambda v: f"{v:.3f}".replace(".", ","))
    x["Long. (m)"] = x["Long. (m)"].map(lambda v: f"{v:.1f}".replace(".", ","))
    x["Évacuée le"] = x["Évacuée le"].map(lambda d: f"{d:%d/%m/%Y}" if pd.notna(d) else "")
    return x.to_csv(index=False, sep=";").encode("utf-8-sig")


def a_dernier_lv() -> bool:
    """Colonnes « dernier LV » de Billonnage (créées par Billon_app, puis synchronisées) disponibles en ligne ?"""
    try:
        return bool(q("SELECT 1 FROM information_schema.columns WHERE table_schema = 'public' "
                      "AND table_name = 'billonnage' AND column_name = 'dernier_lv'"))
    except Exception:
        return False


def liste_sites() -> list[str]:
    """Sites présents en base (colonne SITE créée par Billon_app puis synchronisée) ; vide tant qu'elle n'existe pas."""
    try:
        if not q("SELECT 1 FROM information_schema.columns WHERE table_schema = 'public' "
                 "AND table_name = 'billonnage' AND column_name = 'site'"):
            return []
        return [r["v"] for r in q("SELECT DISTINCT UPPER(TRIM(site)) AS v FROM billonnage "
                                  "WHERE TRIM(COALESCE(site,'')) <> '' ORDER BY 1")]
    except Exception:
        return []


def recherche_criteres():
    """Recherche multicritères : essence, titre, état, période d'évacuation, LV, camion, séquence, DF10."""
    try:
        titres, essences = listes_filtres()
    except Exception:
        titres, essences = [], []
    tit, ess = filtres_globaux()   # titres / essences : filtres du haut de page (pas de doublon ici)
    filtres_actifs(tit, ess)
    st.markdown('<div class="m4-sec" style="margin-top:.5rem">État des billes</div>', unsafe_allow_html=True)
    etat = seg("État", ETATS, default="Toutes", key="c_etat", label_visibility="collapsed") or "Toutes"
    st.markdown('<div class="m4-sec" style="margin-top:.5rem">Période d\'évacuation</div>', unsafe_allow_html=True)
    du, au = choix_periode("crit")
    try:
        sits = [r["v"] for r in q("SELECT DISTINCT UPPER(TRIM(situation)) AS v FROM billonnage "
                                  "WHERE TRIM(COALESCE(situation,'')) <> '' ORDER BY 1")]
    except Exception:
        sits = []
    sites = liste_sites()
    with st.expander("Plus de critères (" + ("site, " if sites else "") + "situation, LV, séquence, DF10)"):
        site = (st.multiselect("Site", sites, key="c_site", placeholder="Tous les sites") if sites else [])
        sit = st.multiselect("Situation(s)", sits, key="c_sit", placeholder="Toutes les situations")
        lv = st.text_input("N° LV (un ou plusieurs)", key="c_lv", placeholder="Ex. 123, 124")
        seq = st.text_input("Séquence(s) finissant par", key="c_seq", placeholder="Ex. 457, 1203")
        df10 = st.text_input("DF10 commençant par", key="c_df10", placeholder="Ex. 54756 ou 53629/10")
    f = {"essences": ess, "titres": tit, "etat": etat, "du": du, "au": au, "lv": _jetons(lv),
         "sites": site, "situations": sit, "sequences": _jetons(seq), "df10": _jetons(df10)}
    if not (ess or tit or etat != "Toutes" or du or au or f["lv"] or f["sites"] or f["situations"] or f["sequences"] or f["df10"]):
        st.markdown('<div class="m4-vide">Choisissez un ou plusieurs critères : ils se cumulent '
                    '(ex. Tali + Évacuées + une période).</div>', unsafe_allow_html=True)
        return

    cond, params = conditions_criteres(f)
    with st.spinner("Recherche…"):
        agg = q("SELECT COUNT(*) AS n, COALESCE(SUM(b.volume),0) AS v, "
                f"COUNT(DISTINCT {CLE_LV}) AS lv, COUNT(DISTINCT NULLIF(TRIM(b.camion),'')) AS cam "
                f"FROM billonnage b WHERE {cond}", params)[0]
        par_ess = q("SELECT COALESCE(NULLIF(UPPER(TRIM(b.essence)),''),'Non renseignée') AS e, COUNT(*) AS n, "
                    f"COALESCE(SUM(b.volume),0) AS v FROM billonnage b WHERE {cond} GROUP BY 1 ORDER BY 3 DESC", params)
        rows = q("SELECT b.df10, b.sequence, UPPER(TRIM(b.essence)) AS essence, TRIM(b.titre) AS titre, b.volume, "
                 "b.longueur, b.dgb, b.dpb, b.situation, b.statut, b.numero_lv, "
                 + ("b.dernier_lv, b.date_dernier_mvt, " if a_dernier_lv() else "")
                 + f"{DATE_EVAC} AS date_evac, b.camion, b.code_barre FROM billonnage b WHERE {cond} "
                 f"ORDER BY {DATE_EVAC} NULLS LAST, b.df10 LIMIT %s", params + [MAX_LIGNES_CRITERES])
    st.markdown(f'<div class="m4-resume"><b>Critères :</b> {e(resume_criteres(f))}</div>', unsafe_allow_html=True)
    if not agg["n"]:
        st.markdown('<div class="m4-vide">Aucune bille ne correspond à ces critères.</div>', unsafe_allow_html=True)
        return
    st.markdown('<div class="m4-kpis">'
                + kpi("Billes", f"{int(agg['n']):,}".replace(",", " "), unite="", couleur="#2D6A4F")
                + kpi("Volume", fr(agg["v"]), couleur="#52B788")
                + kpi("LV utilisés", f"{int(agg['lv'])}", unite="", couleur="#C9A27A")
                + kpi("Camions", f"{int(agg['cam'])}", unite="", couleur="#7A4E2D")
                + '</div>', unsafe_allow_html=True)
    if len(par_ess) > 1:
        st.markdown('<div class="m4-legend" style="margin:-.2rem 0 .8rem">' + "".join(
            f'<span><i class="m4-dot" style="background:{couleur_essence("" if r["e"] == "Non renseignée" else r["e"])}"></i>'
            f'{e(r["e"])} <b>{fr(r["v"])} m³</b> · {r["n"]}</span>' for r in par_ess) + "</div>", unsafe_allow_html=True)
    rows.sort(key=lambda r: (r["date_evac"] or date.max, cle_df10(r["df10"])))
    df = pd.DataFrame([{
        "DF10": r["df10"], "Code barre": r["code_barre"], "Séq.": r["sequence"] or "",
        "DGB": _num(r["dgb"]), "DPB": _num(r["dpb"]),
        "Long. (m)": float(r["longueur"] or 0), "Vol. (m³)": float(r["volume"] or 0),
        "Essence": r["essence"] or "", "Titre": r["titre"] or "", "Situation": r["situation"] or "",
        "Statut": icone_statut(r["statut"]), "N° LV": r["numero_lv"] or "", "Évacuée le": r["date_evac"],
        "Camion": r["camion"] or "",
        **({"Dernier LV": r.get("dernier_lv") or "", "Dernier mvt le": (r["date_dernier_mvt"].strftime("%d/%m/%Y") if r.get("date_dernier_mvt") is not None and hasattr(r["date_dernier_mvt"],"strftime") else "")} if "dernier_lv" in r else {}),
        } for r in rows])
    cfg = {"DF10": st.column_config.TextColumn(pinned=True),
           "Vol. (m³)": st.column_config.NumberColumn(format="%.3f"),
           "Long. (m)": st.column_config.NumberColumn(format="%.1f"),
           "Évacuée le": st.column_config.DateColumn(format="DD/MM/YYYY"), **_cfg_dgb(df)}
    exacts = f["lv"] + f["sequences"] + f["df10"]
    if a_des_exacts(df, exacts):
        st.dataframe(styler_exacts(df, exacts), hide_index=True, width="stretch", column_config=cfg,
                     height=min(520, 38 + 35 * len(df)))
        st.caption("Les lignes en gras correspondent exactement au LV, à la séquence ou au DF10 saisi.")
    else:
        st.dataframe(df, hide_index=True, width="stretch", column_config=cfg, height=min(520, 38 + 35 * len(df)))
    st.caption(f"{len(df):,} bille(s) listée(s)".replace(",", " "))
    st.download_button(f"Télécharger la liste complète (CSV, {len(df):,} lignes)".replace(",", " "), csv_billes(df), file_name="recherche_billes.csv", mime="text/csv",
                       width="stretch", key="dl_crit")



def decoder_codes_barres(im) -> list:
    """Lit les codes-barres d'une photo (Code 39, Code 128, EAN, QR…). Plusieurs passes, de la plus rapide à la plus tolérante.
    Moteur principal : zxing-cpp (bien plus tolérant que zbar au flou, au contraste faible et aux barres larges/étroites de
    ratio 2:1 d'un Code 39). Repli : pyzbar si zxing-cpp n'est pas installé."""
    from PIL import Image, ImageOps
    im = ImageOps.exif_transpose(im).convert("L")
    if max(im.size) > 2600:                                    # photos de 12 Mpx : inutile de tout garder
        im.thumbnail((2600, 2600))
    passes = [im, ImageOps.autocontrast(im, cutoff=2)]
    if im.width < 1000:
        passes.append(ImageOps.autocontrast(im.resize((im.width * 2, im.height * 2), Image.BICUBIC), cutoff=2))
    passes.append(ImageOps.autocontrast(im, cutoff=2).point(lambda v: 255 if v > 128 else 0))
    try:
        import zxingcpp
        # Les étiquettes SIGIF 2 sont en Code 39 : on le cherche d'abord (plus rapide, aucun faux positif d'un autre format),
        # puis on retombe sur tous les formats si rien n'est trouvé.
        for restreint in (True, False):
            options = {"formats": zxingcpp.BarcodeFormat.Code39} if restreint else {}
            for p in passes:
                trouves = []
                for r in zxingcpp.read_barcodes(p, try_rotate=True, try_downscale=True, try_invert=True, **options):
                    t = (r.text or "").strip()
                    if t and t not in trouves:
                        trouves.append(t)
                if trouves:
                    return trouves
        return []
    except ImportError:
        from pyzbar.pyzbar import decode
        for p in passes:
            trouves = []
            for c in decode(p):
                t = c.data.decode("utf-8", "ignore").strip()
                if t and t not in trouves:
                    trouves.append(t)
            if trouves:
                return trouves
        return []


# ----- Scanner en direct (flux vidéo, comme une application de lecture de codes-barres) -------------------------------
CDN_ZXING = "https://cdn.jsdelivr.net/npm/@zxing/library@0.21.3/umd/index.min.js"

HTML_SCAN = """
<div class="m4s">
  <button type="button" class="go">Démarrer le scanner</button>
  <div class="zone" hidden>
    <div class="vid">
      <video playsinline muted autoplay></video>
      <div class="vise"></div>
      <div class="etat">Démarrage de la caméra…</div>
    </div>
    <div class="outils">
      <button type="button" class="sec torche" hidden>Lampe</button>
      <button type="button" class="sec stop">Arrêter</button>
    </div>
    <div class="liste"></div>
    <button type="button" class="ajout" hidden>Ajouter</button>
  </div>
</div>
"""

CSS_SCAN = """
.m4s{font-family:inherit;color:inherit}
button{font:inherit;font-weight:600;border-radius:12px;border:1px solid #2D6A4F;padding:.7rem 1rem;cursor:pointer;width:100%;
  background:#2D6A4F;color:#fff;box-shadow:0 2px 6px rgba(20,37,28,.18);-webkit-tap-highlight-color:transparent}
button:active{transform:translateY(1px)}
button.sec{background:#fff;color:#2D6A4F;box-shadow:none}
.vid{position:relative;border-radius:16px;overflow:hidden;background:#0d1b14;aspect-ratio:4/3;box-shadow:0 6px 18px rgba(20,37,28,.28)}
video{width:100%;height:100%;object-fit:cover;display:block}
.vise{position:absolute;left:8%;right:8%;top:32%;bottom:32%;border:2px solid rgba(255,255,255,.9);border-radius:12px;
  box-shadow:0 0 0 999px rgba(0,0,0,.38);pointer-events:none}
.vise::after{content:"";position:absolute;left:6%;right:6%;top:50%;height:2px;background:#ff5252;box-shadow:0 0 8px #ff5252;
  animation:m4bal 1.6s ease-in-out infinite alternate}
@keyframes m4bal{from{top:18%}to{top:82%}}
.etat{position:absolute;left:0;right:0;bottom:0;padding:.55rem .8rem;font-size:.82rem;font-weight:600;color:#fff;text-align:center;
  background:linear-gradient(transparent,rgba(0,0,0,.72))}
.etat.ok{color:#9ff0c0}
.outils{display:flex;gap:.5rem;margin-top:.6rem}
.liste{display:flex;flex-wrap:wrap;gap:.4rem;margin:.6rem 0}
.puce{display:inline-flex;align-items:center;gap:.4rem;background:#E3EFE5;color:#14251C;border:1px solid #B7D3BE;border-radius:999px;
  padding:.3rem .45rem .3rem .75rem;font-size:.88rem;font-weight:700}
.puce b{cursor:pointer;width:1.35rem;height:1.35rem;border-radius:50%;background:#fff;color:#2D6A4F;display:inline-flex;
  align-items:center;justify-content:center;font-size:.85rem;line-height:1}
.zone[hidden],button[hidden]{display:none}
"""

JS_SCAN = """
export default function (component) {
  const { setTriggerValue, parentElement: root } = component;
  const $ = (s) => root.querySelector(s);
  const S = (root.__m4 = root.__m4 || { codes: [], flux: null, actif: false, dernier: "", nb: 0, tour: 0 });
  const video = $("video"), etat = $(".etat"), liste = $(".liste"), zone = $(".zone"), go = $(".go"), ajout = $(".ajout"), torche = $(".torche");
  const canvas = document.createElement("canvas");

  const dire = (t, ok) => { etat.textContent = t; etat.className = "etat" + (ok ? " ok" : ""); };

  const dessiner = () => {
    liste.innerHTML = "";
    S.codes.forEach((c, i) => {
      const p = document.createElement("span"); p.className = "puce"; p.textContent = c;
      const x = document.createElement("b"); x.textContent = "×"; x.onclick = () => { S.codes.splice(i, 1); dessiner(); };
      p.appendChild(x); liste.appendChild(p);
    });
    ajout.hidden = S.codes.length === 0;
    ajout.textContent = S.codes.length === 1 ? "Ajouter ce code" : "Ajouter les " + S.codes.length + " codes";
  };

  const arreter = () => {
    S.actif = false;
    if (S.flux) { S.flux.getTracks().forEach((t) => t.stop()); S.flux = null; }
    video.srcObject = null; zone.hidden = true; go.hidden = false;
  };

  const charger_zxing = () => new Promise((ok, ko) => {
    if (window.ZXing) return ok(window.ZXing);
    const s = document.createElement("script"); s.src = "__CDN__";
    s.onload = () => ok(window.ZXing); s.onerror = () => ko(new Error("lecteur indisponible")); document.head.appendChild(s);
  });

  const preparer = async () => {
    if (S.pret) return;
    if ("BarcodeDetector" in window) {
      try {
        const f = await window.BarcodeDetector.getSupportedFormats();
        const voulus = ["code_39", "code_128", "ean_13", "ean_8", "itf", "codabar", "upc_a", "qr_code"].filter((x) => f.includes(x));
        if (voulus.includes("code_39")) { S.bd = new window.BarcodeDetector({ formats: voulus }); S.pret = true; return; }
      } catch (e) { /* repli sur zxing */ }
    }
    const Z = await charger_zxing();
    const hints = new Map();
    hints.set(Z.DecodeHintType.POSSIBLE_FORMATS, [Z.BarcodeFormat.CODE_39, Z.BarcodeFormat.CODE_128, Z.BarcodeFormat.EAN_13,
      Z.BarcodeFormat.EAN_8, Z.BarcodeFormat.ITF, Z.BarcodeFormat.QR_CODE]);
    hints.set(Z.DecodeHintType.TRY_HARDER, true);
    S.Z = Z; S.lecteur = new Z.MultiFormatReader(); S.lecteur.setHints(hints); S.pret = true;
  };

  // --- Lecteur Code 39 tolérant : n'exige pas de zone blanche autour du code (étiquettes rognées, fond sombre, écran) ---
  const C39 = {
    nnnwwnwnn: "0", wnnwnnnnw: "1", nnwwnnnnw: "2", wnwwnnnnn: "3", nnnwwnnnw: "4", wnnwwnnnn: "5", nnwwwnnnn: "6", nnnwnnwnw: "7",
    wnnwnnwnn: "8", nnwwnnwnn: "9", wnnnnwnnw: "A", nnwnnwnnw: "B", wnwnnwnnn: "C", nnnnwwnnw: "D", wnnnwwnnn: "E", nnwnwwnnn: "F",
    nnnnnwwnw: "G", wnnnnwwnn: "H", nnwnnwwnn: "I", nnnnwwwnn: "J", wnnnnnnww: "K", nnwnnnnww: "L", wnwnnnnwn: "M", nnnnwnnww: "N",
    wnnnwnnwn: "O", nnwnwnnwn: "P", nnnnnnwww: "Q", wnnnnnwwn: "R", nnwnnnwwn: "S", nnnnwnwwn: "T", wwnnnnnnw: "U", nwwnnnnnw: "V",
    wwwnnnnnn: "W", nwnnwnnnw: "X", wwnnwnnnn: "Y", nwwnwnnnn: "Z", nwnnnnwnw: "-", wwnnnnwnn: ".", nwwnnnwnn: " ", nwnnwnwnn: "*",
    nwnwnwnnn: "$", nwnwnnnwn: "/", nwnnnwnwn: "+", nnnwnwnwn: "%",
  };
  const C39R = {};
  Object.keys(C39).forEach((k) => { C39R[k.split("").reverse().join("")] = C39[k]; });

  const lire_runs = (runs, table) => {
    for (let s = 0; s + 20 < runs.length; s++) {
      if (!runs[s].dark) continue;
      let k = s, texte = "", etoile = false;
      for (let n = 0; n < 44; n++) {
        if (k + 8 >= runs.length) { texte = ""; break; }
        const w = []; for (let i = 0; i < 9; i++) w.push(runs[k + i].w);
        const etroit = w.slice().sort((a, b) => a - b)[2];
        for (const i of [0, 8]) if (w[i] > 5 * etroit) w[i] = etroit;                // 1re / dernière barre fondue dans un fond sombre : étroite
        const ordre = w.map((_, i) => i).sort((a, b) => w[b] - w[a]);
        const larges = ordre.slice(0, 3), etroits = ordre.slice(3);
        if (w[larges[2]] < 1.1 * w[etroits[0]]) { texte = ""; break; }
        const c = table[w.map((_, i) => (larges.includes(i) ? "w" : "n")).join("")];
        if (!c) { texte = ""; break; }
        if (n === 0) { if (c !== "*") break; etoile = true; }
        else if (c === "*") { return texte.length >= 4 ? texte : ""; }
        else texte += c;
        k += 9;
        if (k >= runs.length) { texte = ""; break; }
        const unite = (w[etroits[0]] + w[etroits[etroits.length - 1]]) / 2;
        if (runs[k].dark || runs[k].w > 2.4 * unite) { texte = ""; break; }       // espace inter-caractère
        k += 1;
      }
      if (!etoile) continue;
    }
    return "";
  };

  const decoder_ligne = (lum) => decoder_ligne_l(lum, true) || decoder_ligne_l(lum, false);
  const decoder_ligne_l = (lum, lisse) => {
    const n = lum.length;
    const sm = new Float32Array(n);
    for (let i = 0; i < n; i++) sm[i] = lisse ? (lum[Math.max(0, i - 1)] + lum[i] + lum[Math.min(n - 1, i + 1)]) / 3 : lum[i];
    const tri = Array.from(sm).sort((a, b) => a - b);
    const lo = tri[Math.floor(n * 0.06)], hi = tri[Math.floor(n * 0.94)];
    if (hi - lo < 35) return "";
    const fen = Math.max(24, Math.round(n / 8)), cum = new Float32Array(n + 1);
    for (let i = 0; i < n; i++) cum[i + 1] = cum[i] + sm[i];
    const seuils = [(i) => (lo + hi) / 2, (i) => lo + 0.62 * (hi - lo), (i) => lo + 0.38 * (hi - lo), (i) => { const a = Math.max(0, i - fen), b = Math.min(n, i + fen); return (cum[b] - cum[a]) / (b - a) - 4; }];
    for (const seuil of seuils) {
      const runs = []; let dark = sm[0] < seuil(0), w = 0;
      for (let i = 0; i < n; i++) {
        const d = sm[i] < seuil(i);
        if (d === dark) w++; else { runs.push({ dark, w }); dark = d; w = 1; }
      }
      runs.push({ dark, w });
      const t = lire_runs(runs, C39) || lire_runs(runs.slice().reverse(), C39R);
      if (t) return t;
    }
    return "";
  };

  const lire_tolerant = () => {
    const w = video.videoWidth, h = video.videoHeight;
    if (!w) return [];
    const cw = Math.min(w, 1280), ch = Math.round((h * cw) / w);
    canvas.width = cw; canvas.height = ch;
    const c = canvas.getContext("2d", { willReadFrequently: true });
    c.drawImage(video, 0, 0, cw, ch);
    const y0 = Math.round(ch * 0.3), y1 = Math.round(ch * 0.7), pas = Math.max(2, Math.round((y1 - y0) / 11));
    const votes = {};
    for (let y = y0; y <= y1; y += pas) {
      const d = c.getImageData(0, y, cw, 1).data, lum = new Uint8Array(cw);
      for (let i = 0; i < cw; i++) lum[i] = (d[4 * i] * 77 + d[4 * i + 1] * 150 + d[4 * i + 2] * 29) >> 8;
      const t = decoder_ligne(lum);
      if (t) votes[t] = (votes[t] || 0) + 1;
    }
    return Object.keys(votes).filter((t) => votes[t] >= 2);                          // lu sur au moins 2 lignes de la même image
  };

  const lire_standard = async () => {
    if (S.bd) return (await S.bd.detect(video)).map((r) => r.rawValue);
    const w = video.videoWidth, h = video.videoHeight;
    if (!w) return [];
    const cw = Math.min(w, 1280), ch = Math.round((h * cw) / w);
    S.tour++;
    const pivote = S.tour % 3 === 0;                              // un essai sur trois à la verticale
    canvas.width = pivote ? ch : cw; canvas.height = pivote ? cw : ch;
    const c = canvas.getContext("2d", { willReadFrequently: true });
    c.save();
    if (pivote) { c.translate(ch, 0); c.rotate(Math.PI / 2); }
    c.drawImage(video, 0, 0, cw, ch);
    c.restore();
    const Z = S.Z;
    try {
      const bmp = new Z.BinaryBitmap(new Z.HybridBinarizer(new Z.HTMLCanvasElementLuminanceSource(canvas)));
      return [S.lecteur.decode(bmp).getText()];
    } catch (e) { return []; }
  };

  const lire = async () => {
    const r = await lire_standard();
    return r.length ? r : lire_tolerant();
  };

  const boucle = async () => {
    if (!S.actif) return;
    try {
      const trouves = await lire();
      for (const t of trouves.map((x) => (x || "").trim()).filter(Boolean)) {
        if (t === S.dernier) S.nb++; else { S.dernier = t; S.nb = 1; }
        if (S.nb >= 2 && !S.codes.includes(t)) {
          S.codes.push(t); dessiner(); dire("Lu : " + t, true);
          if (navigator.vibrate) navigator.vibrate(70);
        } else if (S.codes.includes(t)) {
          dire("Déjà lu : " + t, true);
        }
      }
      if (!trouves.length && S.codes.length === 0) dire("Placez le code dans le cadre, à l'horizontale");
    } catch (e) { /* image pas prête */ }
    setTimeout(boucle, 90);
  };

  const demarrer = async () => {
    go.hidden = true; zone.hidden = false; dire("Démarrage de la caméra…");
    try {
      await preparer();
      S.flux = await navigator.mediaDevices.getUserMedia({
        audio: false,
        video: { facingMode: { ideal: "environment" }, width: { ideal: 1920 }, height: { ideal: 1080 } },
      });
      const piste = S.flux.getVideoTracks()[0];
      try { await piste.applyConstraints({ advanced: [{ focusMode: "continuous" }] }); } catch (e) { /* non géré */ }
      const cap = piste.getCapabilities ? piste.getCapabilities() : {};
      let lampe = false;
      torche.hidden = !cap.torch;
      torche.onclick = async () => { lampe = !lampe; try { await piste.applyConstraints({ advanced: [{ torch: lampe }] }); } catch (e) { /* ignoré */ } };
      video.srcObject = S.flux; await video.play();
      S.actif = true; S.dernier = ""; S.nb = 0; dire("Placez le code dans le cadre, à l'horizontale"); boucle();
    } catch (e) {
      arreter();
      const refus = e && (e.name === "NotAllowedError" || e.name === "SecurityError");
      go.textContent = refus ? "Caméra refusée — autorisez-la puis réessayez" : "Scanner indisponible (" + (e && e.message ? e.message : e) + ") — réessayer";
    }
  };

  go.onclick = () => { go.textContent = "Démarrer le scanner"; demarrer(); };
  $(".stop").onclick = arreter;
  ajout.onclick = () => { setTriggerValue("ajout", { codes: S.codes.slice(), t: Date.now() }); S.codes = []; dessiner(); arreter(); };
  document.onvisibilitychange = () => { if (document.hidden) arreter(); };
  dessiner();
  return () => { arreter(); };
}
""".replace("__CDN__", CDN_ZXING)


@st.cache_resource
def _composant_scan():
    return st.components.v2.component("m4_scanner", html=HTML_SCAN, css=CSS_SCAN, js=JS_SCAN)


def widget_scan_codebarre(cle_cible: str, key_cam: str):
    """Scanner en direct (flux vidéo, mise au point continue, lecture répétée) ; secours : photo de l'étiquette."""
    with st.expander("📷 Scanner un code-barres avec la caméra", expanded=False):
        res = _composant_scan()(key=f"live_{key_cam}", on_ajout_change=lambda: None)
        recu = getattr(res, "ajout", None)
        if recu and recu.get("codes"):
            actuel = st.session_state.get(cle_cible, "")
            deja = set(actuel.split())
            nouveaux = [c for c in recu["codes"] if c not in deja]
            if nouveaux:
                st.session_state[cle_cible] = (actuel + "\n" + "\n".join(nouveaux)).strip() if actuel else "\n".join(nouveaux)
            st.toast(f"{len(nouveaux)} code(s) ajouté(s)" if nouveaux else "Codes déjà dans la liste", icon=":material/check_circle:")
        st.caption("Placez l'étiquette dans le cadre, à l'horizontale ; chaque code lu s'ajoute à la liste, puis « Ajouter ».")



def _signaler_recenses_non_abattus(introuvables: list[str]) -> list[str]:
    """Codes absents d'Abattage/Billonnage mais présents à l'inventaire : arbre recensé, pas encore abattu. Retourne le reste."""
    restes = []
    for j in introuvables:
        inv, dispo = _inventaire_pour(j.strip(), "", "")
        if inv:
            st.info(f"**{j}** : arbre recensé à l'inventaire, **pas encore abattu** — "
                    f"{str(inv.get('essence') or '').upper()} · Ø {_gn(inv.get('diametre')) or '–'} cm"
                    + (f" · bloc {inv['bloc']}" if inv.get("bloc") else "") + (f" · qualité {inv['qualite']}" if inv.get("qualite") else ""))
        else:
            restes.append(j)
    return restes


# ---------------------------------------------------------------------------
# Carte LV : affichée en tête des résultats quand on saisit / scanne un N° LV ou un CB LV
# ---------------------------------------------------------------------------
@st.cache_data(ttl=TTL_DONNEES, show_spinner=False)
def _billes_du_lv(jeton: str) -> list[dict]:
    return q("SELECT b.df10, b.code_barre, UPPER(TRIM(b.essence)) AS essence, TRIM(b.titre) AS titre, b.dgb, b.dpb, b.longueur, b.volume, "
             "b.statut, b.situation, b.numero_lv, b.code_barre_lv, b.date_evacuation, b.camion FROM billonnage b "
             "WHERE UPPER(TRIM(b.numero_lv)) = %s OR UPPER(TRIM(b.code_barre_lv)) = %s ORDER BY b.df10", [jeton, jeton])


def lv_vises(jetons, filles: dict) -> list[str]:
    """Jetons saisis qui désignent un LV (N° ou CB LV) parmi les billes déjà chargées, dans l'ordre de saisie, sans doublon."""
    connus = set()
    for lignes in filles.values():
        for r in lignes:
            for c in ("numero_lv", "code_barre_lv"):
                v = str(r.get(c) or "").strip().upper()
                if v:
                    connus.add(v)
    vus, res = set(), []
    for j in jetons:
        u = str(j).strip().upper()
        if u in connus and u not in vus:
            vus.add(u)
            res.append(u)
    return res


def carte_lv(jeton: str):
    billes = _billes_du_lv(jeton)
    if not billes:
        return
    num = next((str(r["numero_lv"]).strip() for r in billes if str(r.get("numero_lv") or "").strip()), jeton)
    cbs_lv = sorted({str(r["code_barre_lv"]).strip() for r in billes if str(r.get("code_barre_lv") or "").strip()})
    camions = sorted({str(r["camion"]).strip() for r in billes if str(r.get("camion") or "").strip()})
    chauffeurs = sorted({c for c in (_chauffeur_pour(str(r["code_barre"] or "")) for r in billes[:5] if r["code_barre"]) if c})
    sits = sorted({str(r["situation"]).strip() for r in billes if str(r.get("situation") or "").strip()})
    dates = sorted(r["date_evacuation"] for r in billes if r.get("date_evacuation"))
    sites = sorted(set(_sites_billes(tuple(str(r["code_barre"] or "") for r in billes if r["code_barre"])).values()))
    titres = sorted({r["titre"] for r in billes if r.get("titre")})
    ab = [r for r in billes if str(r.get("statut") or "").strip().upper() == "ABANDON"]
    v_tot = sum(float(r["volume"] or 0) for r in billes)
    n_gr = len({(r["df10"] or "").rsplit("/", 1)[0] for r in billes})
    if dates:
        d1, d2 = _jour(dates[0]), _jour(dates[-1])
        txt_date = f"Évacué le {d1}" if d1 == d2 else f"Évacué du {d1} au {d2}"
    else:
        txt_date = ""
    ligne_transport = " · ".join(e(x) for x in (", ".join(camions), ", ".join(chauffeurs), ", ".join(cbs_lv)) if x)
    ligne_sit = " · ".join(x for x in (txt_date, ("📍 " + e(" / ".join(sits))) if sits else "", e(", ".join(sites))) if x)
    par_ess: dict[str, list] = {}
    for r in billes:
        d = par_ess.setdefault(r["essence"] or "—", [0, 0.0])
        d[0] += 1
        d[1] += float(r["volume"] or 0)
    ess_html = "".join(f'<div class="m4-lv-e"><span>{e(k)}</span><span>{n} bille(s)</span><b>{fr(v)} m³</b></div>'
                       for k, (n, v) in sorted(par_ess.items(), key=lambda kv: -kv[1][1]))
    lignes = ""
    for r in billes[:80]:
        abandon = str(r.get("statut") or "").strip().upper() == "ABANDON"
        lignes += (f'<tr><td><b>{e(r["df10"])}</b></td><td>{e(r["code_barre"] or "")}</td><td>{e(str(r["essence"] or "")[:3])}</td>'
                   f'<td>{_gn(r["dgb"]) or "–"}/{_gn(r["dpb"]) or "–"}</td><td>{fr(r.get("longueur"), 1)}</td><td>{fr(r["volume"])}</td>'
                   f'<td>{"❌" if abandon else "✅"}</td></tr>')
    with st.container(border=True):
        st.markdown(f'<div class="m4-fiche-t"><b>LV N° {e(num)}</b>{badge(str(len(billes)) + " bille(s)", "neutral")}</div>'
                    + (f'<div class="m4-fiche-s">{ligne_transport}</div>' if ligne_transport else "")
                    + (f'<div class="m4-fiche-s">{ligne_sit}</div>' if ligne_sit else ""), unsafe_allow_html=True)
        st.markdown('<div class="m4-kpis three">' + kpi("Volume", fr(v_tot), couleur="#2D6A4F") + kpi("Billes", str(len(billes)), "", "#52B788")
                    + kpi("Grumes", str(n_gr), "", "#6C8EAD") + "</div>", unsafe_allow_html=True)
        st.markdown(f'<div class="m4-lv-es">{ess_html}</div>', unsafe_allow_html=True)
        if titres:
            st.caption("Titre " + " · ".join(titres))
        if ab:
            st.warning(f"{len(ab)} bille(s) en abandon dans ce LV.", icon=":material/warning:")
        st.markdown('<div class="m4-lv-w"><table class="m4-lv-t"><thead><tr><th>DF10</th><th>CB</th><th>Ess.</th><th>DGB/DPB</th><th>L (m)</th><th>m³</th><th></th></tr></thead>'
                    f'<tbody>{lignes}</tbody></table></div>', unsafe_allow_html=True)
        if len(billes) > 80:
            st.caption(f"{len(billes) - 80} bille(s) de plus dans ce LV : voir les fiches des grumes.")


def vue_recherche(seuil: float):
    mode = seg("Type de recherche", [MODE_AUTO, MODE_CRIT], default=MODE_AUTO,
               key="rech_mode", label_visibility="collapsed")
    if mode == MODE_CRIT:
        return recherche_criteres()
    etiquette = "DF10, code barre, N° LV ou séquence"
    exemple = "Ex. 54756/1\n53629/10/2\nCB123456\n2177766\nUn par ligne ou séparés par des virgules."
    aide = ("La page respecte l'ordre de saisie. Un DF10 de bille (53629/10/2) ouvre sa grume mère (53629/10). "
            "Un nombre seul (54756) ouvre toutes les grumes de ce carnet ; s'il ne correspond à aucun DF10, code barre ou LV, "
            "il est cherché comme FIN de séquence (« 457 » trouve 457, 1457, 20457…).")
    cle_saisie = "saisie_auto"
    widget_scan_codebarre(cle_saisie, f"cam_rech_{MODE_AUTO}")
    texte = st.text_area(etiquette, key=cle_saisie, height=90, placeholder=exemple, help=aide)
    if st.button("Rechercher", type="primary", width="stretch", key="btn_rech"):
        st.session_state["recherche_active"] = (MODE_AUTO, texte)
        st.session_state["rech_nb"] = MAX_GRUMES_RECHERCHE
    actif = st.session_state.get("recherche_active")
    if not actif or actif[0] != MODE_AUTO or not actif[1].strip():
        st.markdown('<div class="m4-vide">Saisissez ou scannez un ou plusieurs numéros, puis « Rechercher ».</div>',
                    unsafe_allow_html=True)
        return
    jetons = _jetons(actif[1])
    codes, notes = set(), []
    with st.spinner("Recherche…"):
        grumes, introuvables = trouver_grumes(jetons)
        if introuvables:                                  # repli : le jeton est peut-être la fin d'une séquence
            g_seq, introuvables, codes, notes = trouver_par_sequence(introuvables)
            grumes = grumes + [g for g in g_seq if g not in grumes]
        plafond = st.session_state.get("rech_nb", MAX_GRUMES_RECHERCHE)
        affichees = grumes[:plafond]
        meres, filles = charger_fiches(affichees)
    if introuvables:
        introuvables = _signaler_recenses_non_abattus(introuvables)
    if introuvables:
        st.warning("Introuvable : " + ", ".join(introuvables))
    for n in notes:
        st.info(n)
    if codes:
        st.caption(f"{len(codes)} bille(s) trouvée(s) par leur séquence. Elles sont surlignées.")
    if len(grumes) > len(affichees):
        st.caption(f"{len(grumes)} grumes trouvées — {len(affichees)} affichées.")
    st.caption("Les lignes en gras correspondent exactement à ce que vous avez saisi.")
    lv = lv_vises(jetons, filles)
    for j in lv:
        carte_lv(j)
    if lv:
        with st.expander(f"Fiches des {len(affichees)} grume(s) concernée(s)", icon=":material/forest:", expanded=len(affichees) == 1):
            for g in affichees:
                afficher_fiche(g, meres, filles, seuil, surligner=codes or None, exacts=list(jetons) + sorted(codes))
    else:
        for g in affichees:
            afficher_fiche(g, meres, filles, seuil, surligner=codes or None, exacts=list(jetons) + sorted(codes))
    if len(grumes) > len(affichees):
        if st.button(f"Afficher {min(MAX_GRUMES_RECHERCHE, len(grumes) - len(affichees))} grumes de plus",
                     width="stretch", key="rech_plus"):
            st.session_state["rech_nb"] = plafond + MAX_GRUMES_RECHERCHE
            st.rerun()


# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# Partage : rapports (abattage / exploitation / évacuation) et fiches de grume en image + Excel
# ---------------------------------------------------------------------------
MODELES_PARTAGE = ["Abattage", "Exploitation", "Évacuation"]
ESSENCE_VIDE = "Non renseignée"


def _conditions(col_date: str, du, au, titres, essences, alias: str):
    w, p = [], []
    if du:
        w.append(f"{col_date} >= %s")
        p.append(du)
    if au:
        w.append(f"{col_date} <= %s")
        p.append(au)
    if titres:
        w.append(f"TRIM(COALESCE({alias}.titre,'')) = ANY(%s)")
        p.append(list(titres))
    if essences:
        w.append(f"UPPER(TRIM(COALESCE({alias}.essence,''))) = ANY(%s)")
        p.append(list(essences))
    return w, p


def _nom_essence(v) -> str:
    v = str(v or "").strip()
    return v.title() if v else ESSENCE_VIDE


def _texte_titres(titres: list[str]) -> str:
    titres = [t for t in titres if t]
    if not titres:
        return "Titre non renseigné"
    if len(titres) == 1:
        return f"Titre {titres[0]}"
    visibles = titres[:5]
    reste = len(titres) - len(visibles)
    return "Titres " + " · ".join(visibles) + (f" · + {reste} autres" if reste else "")


def _texte_sous(debut, fin, essences, activite: str) -> str:
    """Période réelle de l'activité : première et dernière date présentes dans les données retenues."""
    if debut and fin and debut != fin:
        s = f"{activite} du {debut:%d/%m/%Y} au {fin:%d/%m/%Y}"
    elif debut or fin:
        s = f"{activite} le {(debut or fin):%d/%m/%Y}"
    else:
        s = f"{activite} : dates non renseignées"
    if essences:
        s += " · " + ", ".join(_nom_essence(x) for x in essences)
    return s


def construire_rapport(modele: str, du, au, titres, essences) -> dict:
    """Données d'une carte de partage. Titres en en-tête, période, nombre et liste de DF10 (et de LV pour l'évacuation)."""
    if modele == "Abattage":
        col, alias, table, etiquette = "a.date", "a", "abattage a", "Rapport d'abattage"
    elif modele == "Exploitation":
        col, alias, table, etiquette = "b.date_billonnage", "b", "billonnage b", "Rapport d'exploitation"
    else:
        col, alias, table, etiquette = DATE_EVAC, "b", "billonnage b", "Rapport d'évacuation"
    w, p = _conditions(col, du, au, titres, essences, alias)
    extra, pextra = [], []
    if modele == "Évacuation":
        extra, pextra = [SIT_EVAC, NON_ABANDON], [SITUATIONS_EVACUEES]
    cond = " AND ".join(["TRUE"] + w + extra)
    prm = p + pextra
    ess_expr = f"COALESCE(NULLIF(UPPER(TRIM({alias}.essence)),''),'{ESSENCE_VIDE.upper()}')"
    df10_col = f"{alias}.df10"

    presents = q(f"SELECT DISTINCT TRIM(COALESCE({alias}.titre,'')) AS t FROM {table} WHERE {cond}", prm)
    titres_aff = sorted({r["t"] for r in presents if r["t"]}) if not titres else list(titres)
    df10 = q(f"SELECT DISTINCT split_part(TRIM({df10_col}),'/',1) AS d FROM {table} "
             f"WHERE TRIM(COALESCE({df10_col},'')) <> '' AND {cond}", prm)
    liste_df10 = sorted({r["d"] for r in df10 if r["d"]}, key=cle_naturelle)
    bornes = q(f"SELECT MIN({col}) AS d, MAX({col}) AS f FROM {table} WHERE {cond}", prm)
    debut, fin = (bornes[0]["d"], bornes[0]["f"]) if bornes else (None, None)
    activite = {"Abattage": "Abattage", "Exploitation": "Exploitation (billonnage)", "Évacuation": "Évacuation"}[modele]
    rap = {"etiquette": etiquette, "titre": _texte_titres(titres_aff), "sous": _texte_sous(debut, fin, essences, activite),
           "nom_fichier": etiquette.lower().replace("'", "").replace(" ", "_"), "listes": [], "listes_excel": []}

    if modele == "Abattage":
        lignes = q(f"SELECT {ess_expr} AS essence, COUNT(*) AS n, COALESCE(SUM(a.volume),0) AS v FROM {table} "
                   f"WHERE {cond} GROUP BY 1", prm)
        nb, vol = sum(int(r["n"]) for r in lignes), sum(float(r["v"]) for r in lignes)
        essences_abattues = [r["essence"] for r in lignes]
        # Permis : volume autorisé par (titre, essence) — seulement pour les essences abattues ; abattu = cumul depuis le début
        auto, cumul = {}, {}   # (titre, essence) -> [volume, pieds]
        if essences_abattues and titres_aff:
            for r in q("SELECT TRIM(titre) AS t, UPPER(TRIM(essence)) AS e, COALESCE(SUM(volume),0) AS v, COALESCE(SUM(pied),0) AS n "
                       "FROM permis WHERE TRIM(titre) = ANY(%s) AND UPPER(TRIM(essence)) = ANY(%s) GROUP BY 1, 2",
                       [list(titres_aff), essences_abattues]):
                auto[(r["t"], r["e"])] = [float(r["v"]), int(r["n"])]
            for r in q("SELECT TRIM(COALESCE(titre,'')) AS t, UPPER(TRIM(essence)) AS e, COALESCE(SUM(volume),0) AS v, COUNT(*) AS n "
                       "FROM abattage WHERE TRIM(COALESCE(titre,'')) = ANY(%s) AND UPPER(TRIM(essence)) = ANY(%s) GROUP BY 1, 2",
                       [list(titres_aff), essences_abattues]):
                cumul[(r["t"], r["e"])] = [float(r["v"]), int(r["n"])]
        par_ess: dict[str, list] = {}   # essence -> [autorisé m³, abattu m³, pieds autorisés, grumes abattues, dépassement ?]
        for cle in set(auto) | set(cumul):
            av, ap = auto.get(cle, [0.0, 0]), cumul.get(cle, [0.0, 0])
            x = par_ess.setdefault(cle[1], [0.0, 0.0, 0, 0, False])
            x[0] += av[0]
            x[1] += ap[0]
            x[2] += av[1]
            x[3] += ap[1]
            x[4] = x[4] or ap[0] > av[0] + 0.0005 or ap[1] > av[1]
        L, rouges_cases = [], []
        for e_, x in sorted(par_ess.items(), key=lambda kv: -kv[1][1]):
            if x[0] <= 0.0005 and x[1] <= 0.0005:
                continue   # essence sans permis ni abattage en volume : non affichée
            i = len(L)
            L.append([_nom_essence(e_), f"{x[3]} / {x[2]}", x[0], x[1], x[0] - x[1]])
            if x[3] > x[2] or x[4]:
                rouges_cases.append([i, 1])
            if x[1] > x[0] + 0.0005 or x[4]:
                rouges_cases += [[i, 3], [i, 4]]
        tot = [sum(x[2] for x in L), sum(x[3] for x in L), sum(x[4] for x in L)]
        n_ab, n_au = sum(x[3] for x in par_ess.values()), sum(x[2] for x in par_ess.values())
        rap["kpis"] = [(nombre_p(nb, 0), "Grumes", None), (nombre_p(len(liste_df10), 0), "DF10", None),
                       (nombre_p(vol), "Volume m³", "t")]
        rap["colonnes"] = [{"nom": "Essence"}, {"nom": "Pieds", "al": "r", "w": 62}, {"nom": "Autorisé", "g": "m3", "w": 66},
                           {"nom": "Abattu", "g": "m3", "w": 66}, {"nom": "Reste", "g": "m3", "w": 66}]
        rap["lignes"] = L
        rap["total"] = ["TOTAL", f"{n_ab} / {n_au}", *tot]
        if n_ab > n_au:
            rouges_cases.append([len(L), 1])
        if tot[1] > tot[0] + 0.0005:
            rouges_cases += [[len(L), 3], [len(L), 4]]
        rap["rouges_cases"] = rouges_cases
        rap["titre_table"] = "Permis par essence · abattu cumulé"
        rap["taille_table"] = 11
        rap["note"] = "Pieds = abattus / autorisés · en rouge : dépassement (billes ou volume)"
    elif modele == "Exploitation":
        lignes = q(f"SELECT {ess_expr} AS essence, "
                   f"COUNT(*) FILTER (WHERE {NON_ABANDON}) AS n, "
                   f"COALESCE(SUM(b.volume) FILTER (WHERE {NON_ABANDON}),0) AS v, "
                   f"COUNT(*) FILTER (WHERE NOT ({NON_ABANDON})) AS n_ab, "
                   f"COALESCE(SUM(b.volume) FILTER (WHERE NOT ({NON_ABANDON})),0) AS ab "
                   f"FROM {table} WHERE {cond} GROUP BY 1 ORDER BY v DESC", prm)
        L = [[_nom_essence(r["essence"]), int(r["n"]), float(r["v"])] for r in lignes if abs(float(r["v"])) > 0.0005]
        nb, vol = sum(x[1] for x in L), sum(x[2] for x in L)
        n_ab, v_ab = sum(int(r["n_ab"]) for r in lignes), sum(float(r["ab"]) for r in lignes)
        rap["kpis"] = [(nombre_p(nb, 0), "Billes exploitées", None), (nombre_p(len(liste_df10), 0), "DF10", None),
                       (nombre_p(vol), "Exploité m³", "t")]
        rap["colonnes"] = [{"nom": "Essence"}, {"nom": "Billes", "g": "int", "w": 56}, {"nom": "Exploité m³", "g": "m3", "w": 88}]
        rap["lignes"] = L
        rap["total"] = ["TOTAL", nb, vol]
        rap["titre_table"] = "Exploité par essence"
        rap["infos"] = [("Billes abandonnées", f"{nombre_p(n_ab, 0)} · {nombre_p(v_ab)} m³")]
    else:
        lignes = q(f"SELECT {ess_expr} AS essence, COUNT(*) AS n, "
                   f"COALESCE(SUM(b.volume),0) AS v FROM {table} WHERE {cond} GROUP BY 1 ORDER BY v DESC", prm)
        lvs = q(f"SELECT DISTINCT {CLE_LV} AS lv FROM {table} WHERE {cond} AND {CLE_LV} IS NOT NULL", prm)
        liste_lv = sorted({r["lv"] for r in lvs if r["lv"]}, key=cle_naturelle)
        L = [[_nom_essence(r["essence"]), int(r["n"]), float(r["v"])] for r in lignes if abs(float(r["v"])) > 0.0005]
        nb, vol = sum(x[1] for x in L), sum(x[2] for x in L)
        rap["kpis"] = [(nombre_p(nb, 0), "Billes évacuées", None), (nombre_p(len(liste_lv), 0), "LV", None),
                       (nombre_p(vol), "Volume m³", "t")]
        rap["colonnes"] = [{"nom": "Essence"}, {"nom": "Billes", "g": "int", "w": 56}, {"nom": "Volume m³", "g": "m3", "w": 88}]
        rap["lignes"], rap["total"] = L, ["TOTAL", nb, vol]
        rap["titre_table"] = "Évacué par essence"
        if liste_lv:
            rap["listes"].append((f"{len(liste_lv)} LV utilisés", liste_lv, True))
            rap["listes_excel"].append(("LV", liste_lv))
    if liste_df10 and modele != "Évacuation":
        rap["listes"].insert(0, (f"{len(liste_df10)} DF10 {'utilisés' if modele == 'Abattage' else 'exploités'}", liste_df10, False))
        rap["listes_excel"].insert(0, ("DF10", liste_df10))
    rap["vide"] = not rap["lignes"]
    return rap


def nombre_p(v, dec=3) -> str:
    return partage.nombre(v, dec)


@st.cache_data(ttl=TTL_DONNEES, show_spinner=False)
def fabriquer_fichiers(rap_json: str, avec_excel: bool = True) -> tuple:
    import json
    rap = json.loads(rap_json)
    for k in ("kpis", "lignes", "listes", "infos", "listes_excel"):
        if k in rap:
            rap[k] = [tuple(x) if isinstance(x, list) else x for x in rap[k]]
    return partage.rendre_png(rap), (partage.rendre_xlsx(rap) if avec_excel else b"")


def _fichiers(rap: dict, avec_excel: bool = True) -> tuple:
    import json
    return fabriquer_fichiers(json.dumps(rap, ensure_ascii=False, default=str), avec_excel)


SHARE_HTML = """<!doctype html><meta charset="utf-8"><style>
html,body{margin:0 0 8px;background:transparent;font-family:Inter,system-ui,sans-serif}
button{width:100%;display:flex;align-items:center;justify-content:center;gap:10px;border:0;cursor:pointer;
 padding:14px 18px;border-radius:14px;color:#fff;font:600 15px Inter,system-ui,sans-serif;letter-spacing:.01em;
 background:linear-gradient(135deg,#c96a3f,#b5532f);box-shadow:0 4px 10px rgba(181,83,47,.25);transition:transform .12s}
button:active{transform:scale(.98)}svg{width:20px;height:20px}
</style><button id="b"><svg viewBox="0 0 24 24" fill="none" stroke="#fff" stroke-width="2" stroke-linecap="round"
 stroke-linejoin="round"><path d="M12 3v12"/><path d="M8 7l4-4 4 4"/><path d="M5 12v7a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2v-7"/></svg>
 <span>Partager l'image</span></button>
<div id="m" style="font:12.5px/1.4 Inter,system-ui,sans-serif;color:#8a6d3b;margin:6px 4px 0;display:none"></div>
<script>
const uri="__URI__",nom="__NOM__",texte=__TEXTE__;
const lab=document.querySelector("#b span"),orig=lab.textContent;
let fichier=null;
fetch(uri).then(r=>r.blob()).then(b=>{fichier=new File([b],nom,{type:"image/png"});}).catch(()=>{});
const msg=t=>{const m=document.getElementById("m");m.textContent=t;m.style.display="block";};
const flash=t=>{lab.textContent=t;setTimeout(()=>{lab.textContent=orig;},6000);};
function enregistrer(){try{const a=document.createElement("a");a.href=uri;a.download=nom;document.body.appendChild(a);a.click();a.remove();}catch(e){}}
function repli(){
  enregistrer();
  flash("Partage direct indisponible");
  msg("Utilisez le bouton « Enregistrer l'image » juste en dessous, puis envoyez le fichier depuis votre galerie ou WhatsApp.");
}
document.getElementById("b").onclick=()=>{
  document.getElementById("m").style.display="none";
  const cibles=[];
  try{if(window.parent&&window.parent.navigator&&window.parent.navigator.share)cibles.push(window.parent.navigator);}catch(e){}
  if(navigator.share)cibles.push(navigator);
  if(!fichier||!cibles.length){repli();return;}
  const essayer=i=>{
    if(i>=cibles.length){repli();return;}
    const n=cibles[i];
    try{
      if(n.canShare&&!n.canShare({files:[fichier]})){essayer(i+1);return;}
      n.share({files:[fichier],title:texte,text:texte}).catch(err=>{
        if(err&&err.name==="AbortError")return;
        essayer(i+1);
      });
    }catch(e){essayer(i+1);}
  };
  essayer(0);
};
</script>"""


def bouton_partager(png: bytes, nom_fichier: str, texte: str):
    """Bouton moderne : ouvre la feuille de partage du téléphone (WhatsApp…) ; à défaut, enregistre l'image."""
    import json
    uri = "data:image/png;base64," + base64.b64encode(png).decode()
    st.iframe(SHARE_HTML.replace("__URI__", uri).replace("__NOM__", nom_fichier)
                    .replace("__TEXTE__", json.dumps(texte, ensure_ascii=False)), height=112)



# ---------------------------------------------------------------------------
# Instantané hors connexion : un fichier HTML autonome (voir hors_ligne.py)
# ---------------------------------------------------------------------------
def _r(v, d=3):
    return None if v is None else round(float(v), d)


def collecter_instantane() -> dict:
    """Toutes les données utiles à la consultation sans réseau (sans filtres : ils se règlent dans le fichier)."""
    df = charger_donnees()
    st_rows = [[r["essence"], r["titre"], _r(r["abattu"]), int(r["n_abattu"]), _r(r["billonne"]), int(r["n_billes"]),
                _r(r["abandon"]), _r(r["evacue"]), _r(r["usine"]), int(r["n_usine"]), _r(r["perte_base"]),
                _r(r["perte_filles"]), int(r["n_grumes_b"])] for r in df.to_dict("records")]
    ev = charger_evac()
    ev_rows = [[r.essence, r.titre, None if pd.isna(r.date) else f"{r.date:%Y-%m-%d}",
                None if pd.isna(r.lv) else str(r.lv), None if pd.isna(r.camion) else str(r.camion), _r(r.volume)]
               for r in ev.itertuples()]
    ra, rb = racine_sql("a.df10"), racine_sql("b.df10")
    meres = q(f"SELECT {ra} AS grume, MAX(UPPER(TRIM(a.essence))) AS essence, MAX(TRIM(a.titre)) AS titre, "
              "COALESCE(SUM(a.volume),0) AS volume, MIN(a.date::text) AS date "
              "FROM abattage a WHERE TRIM(COALESCE(a.df10,'')) <> '' GROUP BY 1")
    filles = q(f"SELECT {rb} AS grume, b.df10, b.sequence, b.code_barre, b.longueur, b.volume, b.statut, b.situation, "
               "b.numero_lv, UPPER(TRIM(b.essence)) AS essence, TRIM(b.titre) AS titre "
               "FROM billonnage b WHERE TRIM(COALESCE(b.df10,'')) <> ''")
    grumes: dict[str, list] = {}
    for m in meres:
        grumes[m["grume"]] = [m["grume"], m["essence"] or "", m["titre"] or "", _r(m["volume"]),
                              (m["date"] or "")[:10], None, []]
    for f in sorted(filles, key=lambda r: cle_df10(r["df10"])):
        g = grumes.setdefault(f["grume"], [f["grume"], f["essence"] or "", f["titre"] or "", 0.0, "", None, []])
        g[6].append([f["df10"], f["sequence"], f["code_barre"], _r(f["longueur"], 2), _r(f["volume"]), f["statut"] or "",
                     f["situation"] or "", f["numero_lv"] or ""])
    sync = derniere_synchro()
    try:
        alertes = charger_alertes([], [])
    except Exception:
        alertes = []
    return {"gen": datetime.now(FUSEAU).strftime("%d/%m/%Y à %H:%M"), "synchro": f"{sync:%d/%m/%Y à %H:%M}" if sync else "",
            "st": st_rows, "ev": ev_rows, "al": alertes, "gr": sorted(grumes.values(), key=lambda g: cle_df10(g[0]))}


def panneau_hors_ligne():
    st.markdown("Un **seul fichier** à enregistrer sur le téléphone : il s'ouvre **sans réseau** (aperçu, rapports, "
                "évacuations, recherche de grumes et de billes, alertes de permis). Les chiffres sont ceux d'aujourd'hui, "
                "figés au moment de la préparation.")
    mdp = st.text_input("Mot de passe du fichier (recommandé)", type="password", key="hl_mdp", max_chars=60,
                        placeholder="Au moins 6 caractères")
    st.caption("Les données sont alors chiffrées : sans ce mot de passe, le fichier ne montre rien.")
    if mdp and len(mdp) < 6:
        st.warning("Choisissez au moins 6 caractères.")
    elif not mdp:
        st.markdown('<div class="m4-banniere" style="margin:.2rem 0 .6rem">Sans mot de passe, toute personne qui reçoit le '
                    'fichier voit les données.</div>', unsafe_allow_html=True)
    if st.button("Préparer le fichier", type="primary", width="stretch", icon=":material/cloud_download:", key="hl_go",
                 disabled=bool(mdp) and len(mdp) < 6):
        with st.spinner("Collecte des données…"):
            try:
                octets = hors_ligne.fabriquer_html(collecter_instantane(), mdp)
                st.session_state["hl_fichier"] = (octets, bool(mdp), datetime.now(FUSEAU).strftime("%Y%m%d_%H%M"))
                noter(st.session_state["utilisateur"]["id"], "hors_ligne", "protégé" if mdp else "sans mot de passe")
            except Exception:
                journal.exception("Instantané hors connexion")
                st.error("Préparation impossible pour le moment. Réessayez dans un instant.")
    prete = st.session_state.get("hl_fichier")
    if prete:
        octets, protege, horo = prete
        st.download_button(f"Télécharger ({len(octets) / 1024 / 1024:.1f} Mo)", octets, file_name=f"Mich4Track_{horo}.html",
                           mime="text/html", width="stretch", icon=":material/download:", key="hl_dl")
        st.caption(("Protégé par mot de passe. " if protege else "") +
                   "Ouvrez-le avec Chrome ou Safari ; vous pouvez aussi l'envoyer par WhatsApp. "
                   "Il ne se met pas à jour tout seul : préparez-en un nouveau quand vous avez du réseau.")

@st.dialog("Partager", width="small")
def dialogue_partage():
    if seg("Quoi", ["Carte de rapport", "Hors connexion"], default="Carte de rapport", key="pt_quoi",
           label_visibility="collapsed") == "Hors connexion":
        panneau_hors_ligne()
        return
    try:
        titres_dispo, essences_dispo = listes_filtres()
    except Exception:
        titres_dispo, essences_dispo = [], []
    modele = seg("Rapport", MODELES_PARTAGE, default="Évacuation", key="pt_modele",
                                  label_visibility="collapsed") or "Évacuation"
    du, au = choix_periode("pt")
    tit = st.multiselect("Titre(s)", titres_dispo, key="pt_titres", placeholder="Tous les titres")
    ess = st.multiselect("Essence(s)", essences_dispo, key="pt_ess", placeholder="Toutes les essences")
    with st.spinner("Préparation de la carte…"):
        rap = construire_rapport(modele, du, au, tit, ess)
        if rap["vide"]:
            st.markdown('<div class="m4-vide">Aucune donnée pour cette période et ces filtres.</div>', unsafe_allow_html=True)
            return
        png, xlsx = _fichiers(rap)
    jour = datetime.now(FUSEAU).strftime("%Y%m%d")
    bouton_partager(png, f"{rap['nom_fichier']}_{jour}.png", f"{rap['etiquette']} — {rap['titre']} — {rap['sous']}")
    st.download_button("Enregistrer l'image", png, file_name=f"{rap['nom_fichier']}_{jour}.png", mime="image/png", width="stretch",
                       icon=":material/download:", key="pt_png")
    st.download_button("Excel : listes complètes", xlsx, file_name=f"{rap['nom_fichier']}_{jour}.xlsx",
                       mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                       width="stretch", icon=":material/table_view:", key="pt_xlsx")
    st.image(png, width="stretch")


def rapport_fiche(grume: str, mere: dict | None, lignes: list, seuil: float) -> dict:
    v_mere = float(mere["volume"] or 0) if mere else 0.0
    v_filles = sum(float(r["volume"] or 0) for r in lignes)
    v_aban = sum(float(r["volume"] or 0) for r in lignes if str(r["statut"] or "").strip().upper() == "ABANDON")
    statut = statut_grume(v_mere, len(lignes), v_filles, v_aban, seuil)
    perte = (v_mere - v_filles) if lignes else 0.0
    essence, titre = _nom_essence((mere or {}).get("essence")), ((mere or {}).get("titre") or "")
    dg = lambda k: (str(int(mere[k])) if mere and mere.get(k) not in (None, "") else "–")  # noqa: E731
    infos = [("Date d'abattage", f"{mere['date']:%d/%m/%Y}" if mere and mere.get("date") else "–"),
             ("Séquence", str((mere or {}).get("sequence") or "–")),
             ("DGB / DPB", f"{dg('dgb')} / {dg('dpb')} cm"),
             ("Longueur", f"{partage.nombre(mere['longueur'], 1)} m" if mere and mere.get("longueur") not in (None, "") else "–"),
             ("Statut", statut)]
    max_l = 40
    L, rouges = [], set()
    for r in lignes[:max_l]:
        if str(r["statut"] or "").strip().upper() == "ABANDON":
            rouges.add(len(L))
        L.append([r["df10"] or "", r["sequence"] or "", float(r["longueur"] or 0), float(r["volume"] or 0),
                  r["situation"] or "", r["numero_lv"] or ""])
    rap = {"etiquette": "Fiche de grume", "titre": grume, "sous": " · ".join(x for x in (essence, f"Titre {titre}" if titre else "") if x),
           "nom_fichier": "fiche_" + re.sub(r"[^0-9A-Za-z]+", "-", grume).strip("-"),
           "kpis": [(partage.nombre(v_mere), "Abattu m³", None), (partage.nombre(v_filles - v_aban), "Exploité m³", None),
                    (f"{perte:+.3f}".replace(".", ","), "Perte m³", "t")],
           "infos": infos, "titre_table": f"Billes issues de la grume ({len(lignes)})",
           "colonnes": [{"nom": "Bille"}, {"nom": "Séq.", "al": "l", "w": 106}, {"nom": "Long.", "g": "m1", "w": 46},
                        {"nom": "m³", "g": "m3", "w": 50}, {"nom": "Situation", "al": "l", "w": 66}, {"nom": "LV", "al": "l", "w": 34}],
           "lignes": L, "rouges": sorted(rouges), "taille_table": 11, "hauteur_ligne": 25, "listes": [], "listes_excel": []}
    if len(lignes) > max_l:
        rap["note"] = f"+ {len(lignes) - max_l} autres billes (voir la fiche à l'écran)"
    return rap


@st.dialog("Partager la fiche", width="small")
def dialogue_fiche(grume: str, mere: dict | None, lignes: list, seuil: float):
    rap = rapport_fiche(grume, mere, lignes, seuil)
    png, _ = _fichiers(rap, avec_excel=False)
    st.image(png, width="stretch")
    bouton_partager(png, f"{rap['nom_fichier']}.png", f"Fiche de grume {grume} — {rap['sous']}")
    st.download_button("Enregistrer l'image", png, file_name=f"{rap['nom_fichier']}.png", mime="image/png", width="stretch",
                       icon=":material/download:", key="fiche_png")



# ---------------------------------------------------------------------------
# Alertes : dépassements du permis (nombre de tiges et/ou volume)
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# Chargement du parc de rupture : évacuation « virtuelle » → bordereau PDF + CSV (aucune écriture en base)
# ---------------------------------------------------------------------------
MAX_BILLES_CHARGEMENT = 15


def billes_du_parc() -> list[dict]:
    """Billes disponibles au parc de rupture (hors Abandon), prêtes à être chargées."""
    return q("SELECT TRIM(b.df10) AS df10, NULLIF(TRIM(b.sequence),'') AS sequence, NULLIF(TRIM(b.code_barre),'') AS code_barre, "
             "b.longueur, b.dgb, b.dpb, COALESCE(b.volume,0) AS volume, UPPER(TRIM(COALESCE(b.essence,''))) AS essence, "
             "TRIM(COALESCE(b.titre,'')) AS titre FROM billonnage b "
             "WHERE UPPER(TRIM(COALESCE(b.situation,''))) LIKE '%%PARC DE RUPTURE%%' "
             f"AND {NON_ABANDON} AND TRIM(COALESCE(b.df10,'')) <> '' ORDER BY 1")


def noter_bordereau(ref: str, fmt: str, rec: dict | None = None):
    noter(st.session_state["utilisateur"]["id"], "chargement", f"{ref} · {fmt}")
    enregistrer_export(rec)


def csv_lv(billes: list[dict]) -> bytes:
    """CSV « LV » : une seule colonne CODE BARRE (une ligne par bille ayant un code barre)."""
    lignes = ["CODE BARRE"] + [str(b["code_barre"]).strip() for b in billes if b.get("code_barre")]
    return ("\r\n".join(lignes) + "\r\n").encode("utf-8")


def vue_chargement_camion():
    st.markdown("Composez un chargement (**15 billes au plus**) : vous obtenez un bordereau **PDF d'une page** et un "
                "**CSV** pour traitement. Rien n'est modifié dans la base.")
    dispo = billes_du_parc()
    if not dispo:
        st.markdown('<div class="m4-vide">Aucune bille disponible au parc de rupture.</div>', unsafe_allow_html=True)
        return
    par_cle = {}
    for b in dispo:
        par_cle[b["df10"].upper()] = b
        if b["code_barre"]:
            par_cle.setdefault(b["code_barre"].upper(), b)
    st.markdown(f'<div class="m4-sec" style="margin-top:.6rem">1 · Billes <span style="text-transform:none;letter-spacing:0">'
                f'({len(dispo)} disponibles au parc)</span></div>', unsafe_allow_html=True)
    widget_scan_codebarre("ch_coll", "cam_ch_neg")
    collees = st.text_area("Saisissez ou collez les DF10 / codes-barres (un par ligne ou séparés par un espace)",
                           key="ch_coll", height=90, placeholder="Ex. 53629/10/1  53629/10/2")
    st.caption("Touchez en dehors de la zone pour valider : les billes trouvées s’affichent ci-dessous.")
    billes, inconnus, doublons, vus = [], [], 0, set()
    for jeton in _jetons(collees):
        b = par_cle.get(jeton.upper())
        if b is None:
            inconnus.append(jeton)
        elif b["df10"] in vus:
            doublons += 1
        else:
            billes.append(b); vus.add(b["df10"])
    if inconnus:
        st.warning("Introuvable ou indisponible au parc (déjà évacuée, abandon, autre situation) : " + ", ".join(inconnus[:10])
                   + ("…" if len(inconnus) > 10 else "") + " — vérifiez la saisie.")
    if doublons:
        st.info(f"{doublons} doublon(s) ignoré(s).")
    if billes:
        memo0 = st.session_state.get("ch_stamp")
        cod0 = [b["df10"] for b in billes]
        avertir_deja(cod0, chargement.reference(memo0[1], cod0) if memo0 and memo0[0] == "|".join(sorted(cod0)) else None)
    if len(billes) > MAX_BILLES_CHARGEMENT:
        st.error(f"{len(billes)} billes saisies : un chargement est limité à {MAX_BILLES_CHARGEMENT}. Retirez-en "
                 f"{len(billes) - MAX_BILLES_CHARGEMENT}.")
        billes = []
    if billes:
        total = sum(float(b["volume"]) for b in billes)
        lignes_html = "".join(
            f'<tr><td>{i}</td><td><b>{e(b["df10"])}</b></td><td>{e(b["sequence"] or "")}</td><td>{e(b["essence"] or "—")}</td>'
            f'<td>{e(chargement._dim(b["dgb"]))}</td><td>{e(chargement._dim(b["dpb"]))}</td>'
            f'<td>{"" if b["longueur"] is None else fr(b["longueur"], 2)}</td>'
            f'<td><b>{fr(b["volume"])}</b></td><td>{e(b["titre"] or "")}</td></tr>' for i, b in enumerate(billes, 1))
        st.markdown('<style>.m4-chg th,.m4-chg td{padding:.42rem .2rem !important;font-size:.64rem !important;letter-spacing:0 !important;white-space:nowrap}</style><div class="m4-sec">Billes retenues — vérifiez</div><div class="m4-mx-wrap"><table class="m4-mx m4-chg"><thead><tr>'
                    '<th>N°</th><th>DF10</th><th>Séquence</th><th>Essence</th><th>DGB</th><th>DPB</th><th>Long.</th><th>m³</th><th>Titre</th></tr></thead>'
                    f'<tbody>{lignes_html}</tbody></table></div>', unsafe_allow_html=True)
        st.markdown('<div class="m4-kpis">' + kpi("Billes", str(len(billes)), "", "#2D6A4F")
                    + kpi("Volume", fr(total), "m³", "#52B788") + '</div>', unsafe_allow_html=True)
    st.markdown('<div class="m4-sec">2 · Transport</div>', unsafe_allow_html=True)
    chauffeur = (st.selectbox("Chauffeur *", valeurs_transport("chauffeur"), key="ch_chauf", index=None, accept_new_options=True,
                              placeholder="Tapez quelques lettres (ex. Serge) : les chauffeurs connus sont proposés") or "").strip()
    tel = st.text_input("Téléphone du chauffeur", key="ch_tel", max_chars=30)
    camion = (st.selectbox("Camion (immatriculation) *", valeurs_transport("camion"), key="ch_camion", index=None, accept_new_options=True,
                           placeholder="Tapez une partie du numéro (ex. 400) : les camions connus sont proposés") or "").strip()
    remorque = st.text_input("Remorque", key="ch_rem", max_chars=30)
    destination = st.text_input("Destination *", key="ch_dest", max_chars=80, placeholder="Ex. Usine, port, client…")
    jour = st.date_input("Date d'évacuation", value=datetime.now(FUSEAU).date(), key="ch_date", format="DD/MM/YYYY")
    obs = st.text_input("Observation", key="ch_obs", max_chars=120)
    manque = [n for n, v in (("chauffeur", chauffeur), ("camion", camion), ("destination", destination)) if not v.strip()]
    st.markdown('<div class="m4-sec">3 · Documents</div>', unsafe_allow_html=True)
    if not billes or manque:
        st.caption("Sélectionnez au moins une bille et renseignez " + (", ".join(manque) if manque else "le transport") + "."
                   if billes or manque else "Sélectionnez au moins une bille.")
        return
    codes = [b["df10"] for b in billes]
    empreinte = "|".join(sorted(codes))
    memo = st.session_state.get("ch_stamp")
    if not memo or memo[0] != empreinte:
        memo = (empreinte, datetime.now(FUSEAU))
        st.session_state["ch_stamp"] = memo
    stamp = memo[1]
    en_tete = {"reference": chargement.reference(stamp, codes), "date": f"{jour:%Y-%m-%d}",
               "date_texte": f"{jour:%d/%m/%Y} à {stamp:%H:%M}", "chauffeur": chauffeur.strip(), "telephone": tel.strip(),
               "camion": camion.strip().upper(), "remorque": remorque.strip().upper(), "destination": destination.strip(),
               "etabli_par": st.session_state["utilisateur"]["nom"], "observation": obs.strip()}
    pdf = chargement.pdf_bordereau(en_tete, billes)
    csv_ = chargement.csv_bordereau(en_tete, billes)
    nom = en_tete["reference"]
    rec = preparer_export("camion", nom, billes, sum(float(b["volume"]) for b in billes), destination=en_tete["destination"],
                          chauffeur=en_tete["chauffeur"], camion=en_tete["camion"], donnees={"en_tete": en_tete, "billes": billes})
    st.markdown(f'<div class="m4-fiche-s">Référence : <b>{e(nom)}</b></div>', unsafe_allow_html=True)
    st.download_button("Bordereau PDF", pdf, file_name=f"{nom}.pdf", mime="application/pdf", type="primary",
                       width="stretch", icon=":material/picture_as_pdf:", key="ch_pdf",
                       on_click=noter_bordereau, args=(nom, "pdf", rec))
    st.download_button("Fichier CSV", csv_, file_name=f"{nom}.csv", mime="text/csv",
                       width="stretch", icon=":material/table_view:", key="ch_csv", on_click=noter_bordereau, args=(nom, "csv", rec))
    st.download_button("Fichier LV", csv_lv(billes), file_name=f"{nom}_LV.csv", mime="text/csv",
                       width="stretch", icon=":material/barcode:", key="ch_lv", on_click=noter_bordereau, args=(nom, "lv", rec))
    sans_cb = sum(1 for b in billes if not b.get("code_barre"))
    if sans_cb:
        st.caption(f"⚠ {sans_cb} bille(s) sans code barre : absente(s) de la LV.")
    st.caption("Envoyez le CSV (et le PDF) à Michel : le chargement est ensuite traité. "
               "Chaque export est gardé dans l'onglet « Historique » ; une bille déjà exportée est signalée.")



def noter_lot(ref: str, fmt: str, rec: dict | None = None):
    noter(st.session_state["utilisateur"]["id"], "chargement", f"{ref} · {fmt}")
    enregistrer_export(rec)


def _table_html(entetes: list[str], lignes: list[list[str]], classe: str = "") -> str:
    tete = "".join(f"<th>{e(h)}</th>" for h in entetes)
    corps = "".join("<tr>" + "".join(f"<td>{c}</td>" for c in l) + "</tr>" for l in lignes)
    return f'<div class="m4-mx-wrap"><table class="m4-mx m4-chg {classe}"><thead><tr>{tete}</tr></thead><tbody>{corps}</tbody></table></div>'


SHARE_FICHIER_HTML = (SHARE_HTML.replace("image/png", "__MIME__").replace("Partager l'image", "Partager le fichier (WhatsApp…)")
                      .replace("« Enregistrer l'image » juste en dessous, puis envoyez le fichier depuis votre galerie ou WhatsApp",
                               "« Télécharger le CSV » juste en dessous, puis envoyez le fichier depuis vos téléchargements ou WhatsApp"))


def bouton_partager_fichier(octets: bytes, nom: str, mime: str, texte: str):
    """Ouvre la feuille de partage du téléphone (WhatsApp…) avec le fichier ; à défaut, l'enregistre."""
    import json
    uri = f"data:{mime};base64," + base64.b64encode(octets).decode()
    st.iframe(SHARE_FICHIER_HTML.replace("__MIME__", mime).replace("__URI__", uri).replace("__NOM__", nom)
                    .replace("__TEXTE__", json.dumps(texte, ensure_ascii=False)), height=112)


def _charger_contrat():
    f = st.session_state.get("lot_ct_up")
    st.session_state.pop("lot_ct_err", None)
    if f is None:
        st.session_state.pop("lot_ct", None)
        return
    try:
        ct = chargement.contrat_depuis_json(f.getvalue())
    except ValueError as exc:
        st.session_state.pop("lot_ct", None)
        st.session_state["lot_ct_err"] = str(exc)
        return
    st.session_state["lot_ct"] = ct
    st.session_state["lot_txt"] = ct["brouillon"]


def _slug(t: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "_", t.strip()).strip("_")[:40] or "contrat"


def tableau_controle(billes: list[dict], erreurs: list[dict], essence_ref: str) -> str:
    """Toutes les lignes de la feuille, dans l'ordre de saisie ; les erreurs et les billes à signaler sont colorées."""
    par_ligne = {b["ligne"]: ("bille", b) for b in billes}
    par_ligne.update({r["ligne"]: ("err", r) for r in erreurs})
    corps = []
    for no in sorted(par_ligne):
        genre, x = par_ligne[no]
        if genre == "err":
            corps.append(f'<tr class="err"><td class="n">{no}<br>✖</td><td colspan="5" style="white-space:normal;min-width:12rem">'
                         f'<b>{e(x["saisie"])}</b> — <b>{e(x["motif"])}</b><br><small>{e(x["detail"])}</small></td></tr>')
            continue
        b = x
        rouge = bool(chargement.alerte_parc(b))
        diff = bool(chargement.alerte_essence(b, essence_ref))
        cls = ' class="warn"' if (rouge or diff) else ""
        st_ess = ' style="color:#B7791F;font-weight:700"' if diff else ""
        al = chargement.alertes_bille(b, essence_ref)
        motif = ('<br><small style="color:%s;font-weight:700;white-space:normal;display:block;width:5.6rem">%s</small>'
                 % ("#B94A44" if rouge else "#B7791F", e(" · ".join(al)))) if al else ""
        corps.append(
            f'<tr{cls}><td class="n">{no}<br>{"⚠" if (rouge or diff) else "✓"}</td><td><b>{e(b["df10"])}</b>{motif}</td>'
            f'<td>{e(b["sequence"] or "")}</td><td>{e(b["code_barre"] or "")}</td>'
            f'<td{st_ess}>{e(b["essence"] or "—")}</td>'
            f'<td><b>{fr(b["volume"])}</b></td></tr>')
    css = ('<style>.m4-ctl tr.err td{background:rgba(185,74,68,.20) !important;color:var(--text)}'
           '.m4-ctl tr.warn td{background:rgba(217,164,65,.24) !important}'
           '.m4-ctl tr.err td:first-child{border-left:5px solid #B94A44}.m4-ctl tr.warn td:first-child{border-left:5px solid #D9A441}'
           '.m4-ctl th{text-align:left}.m4-ctl thead th{text-align:left !important}.m4-ctl thead th:first-child{text-align:center !important}.m4-ctl td.n{text-align:center;font-weight:700;min-width:0 !important}.m4-ctl tr.err td.n{color:#B94A44}'
           '.m4-ctl th,.m4-ctl td{padding:.4rem .16rem !important;font-size:.58rem !important;letter-spacing:0 !important}</style>')
    tete = "".join(f"<th>{h}</th>" for h in ["L.", "DF10", "Séquence", "Code barre", "Essence", "m³"])
    return (css + f'<div class="m4-mx-wrap"><table class="m4-mx m4-chg m4-ctl"><thead><tr>{tete}</tr></thead>'
            f'<tbody>{"".join(corps)}</tbody></table></div>')


def vue_lot_usine():
    st.markdown("Entrée au **parc usine** : recopiez la feuille du terrain, une bille par ligne. **Un identifiant suffit** : "
                "DF10, séquence complète (`1230296-00813`) ou code-barres (deux, c'est plus sûr : ils sont recoupés). "
                "La page retrouve les billes et exporte la **liste en CSV**, à partager sur WhatsApp. "
                "Une bille hors parc de rupture, ou d'une autre essence que le contrat, est **signalée**. Rien n'est modifié dans la base.")
    mode = seg("Contrat", ["Nouveau", "Continuer"], default="Nouveau", key="lot_mode", label_visibility="collapsed")
    lots: list[dict] = []
    if mode == "Continuer":
        st.file_uploader("Fichier de contrat enregistré (.json)", type=["json"], key="lot_ct_up", on_change=_charger_contrat)
        if st.session_state.get("lot_ct_err"):
            st.error(st.session_state["lot_ct_err"])
        ct = st.session_state.get("lot_ct")
        if not ct:
            st.caption("Chargez le fichier enregistré lors de la dernière séance pour compléter ce contrat.")
            return
        contrat, cree_le, lots = ct["contrat"], ct["cree_le"], ct["lots"]
        ess_mem, pref_mem = ct.get("essence", ""), ct.get("prefixe", "")
        n_prec = sum(l["n"] for l in lots)
        v_prec = sum(l["volume"] for l in lots)
        st.markdown(f'<div class="m4-kpis three">' + kpi("Contrat", e(contrat) or "—", "", "#6C8EAD")
                    + kpi("Déjà exportées", str(n_prec), "", "#2D6A4F") + kpi("Volume", fr(v_prec), "m³", "#52B788") + '</div>',
                    unsafe_allow_html=True)
        st.caption(f"{len(lots)} lot(s) précédent(s) · créé le {cree_le or '—'}. Les billes déjà exportées seront refusées si elles reviennent.")
    else:
        contrat = st.text_input("N° ou nom du contrat *", key="lot_contrat", max_chars=60, placeholder="Ex. CT-2026-014")
        cree_le = f"{datetime.now(FUSEAU):%Y-%m-%d}"
        ess_mem, pref_mem = "", ""
    try:
        toutes_ess = listes_filtres()[1]
    except Exception:
        toutes_ess = []
    AUTO = "Automatique (la plus fréquente)"
    choix_ess = [AUTO] + sorted(set(toutes_ess) | ({ess_mem} if ess_mem else set()))
    ess_choisie = st.selectbox("Essence du contrat", choix_ess, index=choix_ess.index(ess_mem) if ess_mem in choix_ess else 0,
                               key=f"lot_ess_{mode}_{ess_mem}_{contrat if mode == 'Continuer' else ''}")
    ess_fixe = "" if ess_choisie == AUTO else ess_choisie
    st.markdown('<div class="m4-sec" style="margin-top:.6rem">1 · Liste de la feuille</div>', unsafe_allow_html=True)
    texte = st.text_area("Une bille par ligne (DF10, séquence ou code-barres)", key="lot_txt", height=280,
                         placeholder="53629/10/1\n1230296-00813\n53629/10/3  1230296-00815\n…")
    prefixe = st.text_input("N° de lot par défaut (facultatif)", value=pref_mem, key=f"lot_pref_{mode}", max_chars=20,
                            placeholder="Ex. 1230296",
                            ).strip()
    if prefixe:
        st.caption(f"Un numéro seul (ex. 813) sera lu comme {prefixe}-00813.")
    lignes_saisie = [l for l in texte.splitlines() if l.strip() and not l.strip().startswith("#")]
    nlig = len(lignes_saisie)
    st.caption(f"{nlig} ligne(s) saisie(s). Touchez en dehors de la zone pour valider.")
    contrat = (contrat or "").strip()
    deja = {}
    for l in lots:
        for ligne in l["lignes"]:
            deja.setdefault(chargement.lire_ligne(ligne)[0], f"lot {l['ref']} du {l['date']}")
    if nlig:
        st.download_button("Enregistrer le brouillon", chargement.contrat_vers_json(contrat, cree_le, lots, texte, ess_fixe, prefixe),
                           file_name=f"Contrat_{_slug(contrat)}.json", mime="application/json", key="lot_brouillon",
                           icon=":material/save:", width="stretch", disabled=not contrat)
        if not contrat:
            st.caption("Indiquez le nom du contrat pour pouvoir l'enregistrer.")
    if nlig == 0:
        return
    if nlig > chargement.MAX_BILLES_LOT:
        st.error(f"{nlig} lignes : le maximum est {chargement.MAX_BILLES_LOT} billes par liste.")
        return
    cles = chargement.cles_requete(texte)
    if prefixe:
        cles["seq"] = sorted(set(cles["seq"]) | {chargement._seq_norm(f"{prefixe}-{n}") for n in cles["num"]})
    tous = q("SELECT TRIM(b.df10) AS df10, NULLIF(TRIM(b.sequence),'') AS sequence, NULLIF(TRIM(b.code_barre),'') AS code_barre, "
             "b.longueur, b.dgb, b.dpb, COALESCE(b.volume,0) AS volume, UPPER(TRIM(COALESCE(b.essence,''))) AS essence, "
             "TRIM(COALESCE(b.titre,'')) AS titre, TRIM(COALESCE(b.situation,'')) AS situation, "
             "TRIM(COALESCE(b.statut,'')) AS statut FROM billonnage b WHERE UPPER(TRIM(b.df10)) = ANY(%s) "
             "OR UPPER(TRIM(b.code_barre)) = ANY(%s) "
             "OR regexp_replace(TRIM(b.sequence), '(^|-)0+(?=\\d)', '\\1', 'g') = ANY(%s) "
             "OR regexp_replace(regexp_replace(TRIM(b.sequence), '^.*-', ''), '^0+(?=\\d)', '') = ANY(%s)",
             [cles["df10"], cles["cb"], cles["seq"], cles["num"]])
    res = chargement.analyser_saisie(texte, tous, None, deja, prefixe)
    billes, erreurs = res["billes"], res["erreurs"]
    hors = [b for b in billes if chargement.alerte_parc(b)]
    # essence du contrat : choisie en haut ; à défaut, la plus fréquente de la saisie
    essence_ref = ess_fixe or chargement.essence_majoritaire(billes)
    autres = [b for b in billes if chargement.alerte_essence(b, essence_ref)]
    a_signaler = [b for b in billes if chargement.alertes_bille(b, essence_ref)]
    st.markdown('<div class="m4-kpis three">' + kpi("Retenues", str(len(billes)), "", "#2D6A4F")
                + kpi("À signaler", str(len(a_signaler)), "", "#D9A441" if a_signaler else "#8A8F86")
                + kpi("À corriger", str(len(erreurs)), "", "#B94A44" if erreurs else "#8A8F86") + '</div>', unsafe_allow_html=True)
    if hors:
        st.warning(f"{len(hors)} bille(s) hors parc de rupture (déjà évacuées, abandon, autre situation) : "
                   "repérées en rouge ci-dessous et dans la colonne « alerte » du CSV.")
    if autres:
        st.info(f"{len(autres)} bille(s) d'une autre essence que le contrat ({essence_ref}) : conservées, marquées ⚠ "
                "ci-dessous et dans la colonne « alerte » du CSV.")
    if billes or erreurs:
        resume = " · ".join(x for x in (f"✖ {len(erreurs)} à corriger" if erreurs else "",
                                        f"⚠ {len(a_signaler)} à signaler" if a_signaler else "") if x) or "tout est conforme"
        with st.expander(f"Contrôle ligne par ligne — {resume}", expanded=bool(erreurs or a_signaler)):
            st.markdown(tableau_controle(billes, erreurs, essence_ref), unsafe_allow_html=True)
        st.caption("Même ordre que la feuille. Ligne rouge ✖ : à corriger (elle n'est pas exportée). "
                   "Ligne jaune ⚠ : bille conservée mais à signaler (hors parc ou autre essence). Dimensions complètes dans le CSV.")
    if erreurs:
        st.download_button("Erreurs en CSV", chargement.csv_erreurs(erreurs), file_name="erreurs_liste_parc_usine.csv",
                           mime="text/csv", key="lot_err", icon=":material/error:", width="stretch")
    if not billes:
        return
    exclure = bool(hors) and st.checkbox("Ne pas exporter les billes hors parc de rupture", key="lot_excl")
    exportees = [b for b in billes if not (exclure and chargement.alerte_parc(b))]
    total = sum(float(b["volume"]) for b in exportees)
    tt = chargement.totaux_titre_essence(exportees)
    st.markdown('<div class="m4-sec">2 · Contrôle par titre et essence</div>', unsafe_allow_html=True)
    st.markdown(_table_html(["Titre", "Essence", "Billes", "m³"], [[e(t), e(es), str(nb), f"<b>{fr(v)}</b>"] for t, es, nb, v in tt]
                            + [["<b>Total</b>", "", f"<b>{len(exportees)}</b>", f"<b>{fr(total)}</b>"]]), unsafe_allow_html=True)
    if lots:
        st.caption(f"Cumul du contrat avec ce lot : {sum(l['n'] for l in lots) + len(exportees)} billes · "
                   f"{fr(sum(l['volume'] for l in lots) + total)} m³.")
    st.markdown('<div class="m4-sec">3 · Export</div>', unsafe_allow_html=True)
    if not contrat:
        st.caption("Indiquez le nom du contrat pour exporter.")
        return
    empreinte = "|".join(sorted(b["df10"] for b in exportees))
    memo = st.session_state.get("lot_stamp")
    if not memo or memo[0] != empreinte:
        memo = (empreinte, datetime.now(FUSEAU))
        st.session_state["lot_stamp"] = memo
    ref = chargement.reference_lot(memo[1], exportees)
    avertir_deja([b["df10"] for b in exportees], ref)
    rec = preparer_export("usine", ref, exportees, total, contrat=contrat, essence=essence_ref,
                          donnees={"billes": exportees, "contrat": contrat})
    nom = f"{_slug(contrat)}_{ref}.csv"
    csv_ = chargement.csv_usine(exportees, essence_ref)
    st.markdown(f'<div class="m4-fiche-s">Lot : <b>{e(ref)}</b> · {len(exportees)} billes · {fr(total)} m³</div>', unsafe_allow_html=True)
    bouton_partager_fichier(csv_, nom, "text/csv", f"Contrat {contrat} — {len(exportees)} billes — {fr(total)} m³")
    st.download_button("Télécharger le CSV", csv_, file_name=nom, mime="text/csv", type="primary", width="stretch",
                       icon=":material/table_view:", key="lot_csv", on_click=noter_lot, args=(f"{contrat} · {ref}", "csv", rec))
    lot = {"ref": ref, "date": f"{memo[1]:%Y-%m-%d}", "n": len(exportees), "volume": round(total, 3),
           "lignes": [f"{b['df10']} {b['sequence'] or ''}".strip() for b in exportees]}
    st.download_button("Enregistrer le contrat (avec ce lot)", chargement.contrat_vers_json(contrat, cree_le, lots + [lot], "", essence_ref, prefixe),
                       file_name=f"Contrat_{_slug(contrat)}.json", mime="application/json", width="stretch",
                       icon=":material/inventory_2:", key="lot_contrat_dl")
    st.caption("1) Partagez le CSV. 2) Enregistrez le contrat mis à jour et **gardez ce fichier** : il sert à « Continuer » plus tard "
               "et évite de renvoyer deux fois les mêmes billes. Cette page ne réserve rien : un autre contrat peut contenir les mêmes billes.")


# ---------------------------------------------------------------------------
# Historique des exports (table mobile_exports : insertion seule ; statut modifiable par la traçabilité)
# ---------------------------------------------------------------------------
STATUTS = ["Émis", "Traité", "Annulé"]


def _plat(o):
    """JSON sûr : Decimal -> float, dates -> texte."""
    import decimal
    if isinstance(o, decimal.Decimal):
        return float(o)
    return str(o)


def preparer_export(genre: str, ref: str, billes: list[dict], volume: float, *, contrat: str = "", destination: str = "",
                    chauffeur: str = "", camion: str = "", essence: str = "", donnees: dict | None = None) -> dict:
    import json
    u = st.session_state["utilisateur"]
    recherche = " ".join(f"{b.get('df10') or ''} {b.get('sequence') or ''} {b.get('code_barre') or ''}" for b in billes).lower()
    return {"reference": ref, "genre": genre, "utilisateur": u["id"], "nom": u["nom"], "role": role_actuel(), "contrat": contrat,
            "destination": destination, "chauffeur": chauffeur, "camion": camion, "essence": essence, "nb": len(billes),
            "volume": round(float(volume), 3), "billes": [b["df10"] for b in billes], "recherche": recherche,
            "donnees": json.dumps(donnees or {}, default=_plat, ensure_ascii=False)}


def enregistrer_export(rec: dict):
    """Garde une trace de l'export (une seule ligne par référence). N'empêche jamais le téléchargement."""
    if not rec:
        return
    ecrire("INSERT INTO public.mobile_exports (reference, genre, utilisateur, nom_affiche, role, contrat, destination, chauffeur, "
           "camion, essence, nb, volume, billes, recherche, donnees) VALUES (%(reference)s,%(genre)s,%(utilisateur)s,%(nom)s,"
           "%(role)s,%(contrat)s,%(destination)s,%(chauffeur)s,%(camion)s,%(essence)s,%(nb)s,%(volume)s,%(billes)s,"
           "%(recherche)s,%(donnees)s::jsonb) ON CONFLICT (reference) DO NOTHING", rec)


def deja_exportees(df10s: list[str], ref_courante: str | None) -> dict:
    """df10 -> (référence, date, auteur, statut) pour les billes déjà présentes dans un export non annulé. Silencieux si la table manque."""
    if not df10s:
        return {}
    try:
        lignes = requete("SELECT reference, genre, to_char(cree_le AT TIME ZONE 'Africa/Douala','DD/MM HH24:MI') AS le, "
                         "nom_affiche, statut, billes FROM public.mobile_exports WHERE statut <> 'Annulé' AND billes && %s "
                         "AND reference <> %s ORDER BY cree_le DESC LIMIT 200", (list(df10s), ref_courante or ""))
    except Exception:
        return {}
    res = {}
    for r in lignes:
        for d in r["billes"]:
            if d in df10s and d not in res:
                res[d] = (r["reference"], r["le"], r["nom_affiche"], r["statut"])
    return res


def avertir_deja(df10s: list[str], ref_courante: str | None):
    trouvees = deja_exportees(df10s, ref_courante)
    if trouvees:
        lst = " · ".join(f"**{d}** ({v[0]}, {v[1]}, {v[2]})" for d, v in list(trouvees.items())[:8])
        st.warning(f"⚠ {len(trouvees)} bille(s) déjà présente(s) dans un export précédent : " + lst
                   + (" …" if len(trouvees) > 8 else "") + " — vérifiez avant d'envoyer. L'export reste possible.")


def _billes_recues(lst: list[dict]) -> list[dict]:
    for b in lst:
        for k in ("volume", "longueur", "dgb", "dpb"):
            if b.get(k) is not None:
                try:
                    b[k] = float(b[k])
                except (TypeError, ValueError):
                    pass
    return lst


def maj_statut(ref: str, statut: str):
    ecrire("UPDATE public.mobile_exports SET statut = %s, statut_par = %s, statut_le = now() WHERE reference = %s",
           (statut, st.session_state["utilisateur"]["id"], ref))
    noter(st.session_state["utilisateur"]["id"], "chargement", f"{ref} · {statut}")


# ---------------------------------------------------------------------------
# Fichier « chargements » : toutes les infos de chargement d'une période, à lire dans Billon_app
# ---------------------------------------------------------------------------
COLS_FICHIER_CHARGEMENTS = ["CODE BARRE", "OPÉRATION", "N° LV", "DATE ÉVACUATION", "CAMION", "CHAUFFEUR", "DESTINATION",
                            "SITE", "DF10", "SÉQUENCE", "ESSENCE", "VOLUME", "TITRE", "REMORQUE", "TÉLÉPHONE",
                            "OBSERVATION", "ÉTABLI PAR", "ÉMIS LE"]


def _date_chargement(rec: dict):
    """Date d'évacuation saisie (en-tête du bordereau) ; à défaut, jour d'émission de l'export."""
    d = rec.get("donnees") or {}
    brut = str((d.get("en_tete") or {}).get("date") or "")[:10]
    try:
        return datetime.strptime(brut, "%Y-%m-%d").date()
    except ValueError:
        return rec["cree_le"].astimezone(FUSEAU).date()


OPERATIONS_FICHIER = ["Tous", "Forêt → Rupture", "Négoce"]


def chargements_periode(du, au, operation: str = "Tous") -> tuple[list[dict], dict]:
    """Lignes (une par bille et par opération) des chargements non annulés dont la date d'évacuation tombe dans la période :
    RUPTURE (Parc Forêt → Parc de rupture, avec SITE) et NEGOCE (départ du Parc de rupture, avec DESTINATION).
    Une bille présente dans plusieurs exports de la même opération ne compte qu'une fois : le plus récent l'emporte."""
    import json
    genres = {"Tous": ["camion", "foret"], "Forêt → Rupture": ["foret"], "Négoce": ["camion"]}.get(operation, ["camion", "foret"])
    lignes = requete("SELECT reference, genre, cree_le, nom_affiche, donnees FROM public.mobile_exports "
                     "WHERE genre = ANY(%s) AND statut <> 'Annulé' ORDER BY cree_le LIMIT 5000", (genres,))
    par_code, sans_cb, remplacees, refs = {}, 0, 0, set()
    for rec in lignes:
        if isinstance(rec.get("donnees"), str):
            try:
                rec["donnees"] = json.loads(rec["donnees"])
            except ValueError:
                rec["donnees"] = {}
        jour = _date_chargement(rec)
        if (du and jour < du) or (au and jour > au):
            continue
        d = rec.get("donnees") or {}
        et = d.get("en_tete") or {}
        rupture = rec.get("genre") == "foret"
        for b in d.get("billes") or []:
            code = str(b.get("code_barre") or "").strip()
            if not code:
                sans_cb += 1
                continue
            cle = (code, rupture)
            if cle in par_code:
                remplacees += 1
            refs.add(rec["reference"])
            par_code[cle] = {
                "CODE BARRE": code, "OPÉRATION": "RUPTURE" if rupture else "NEGOCE", "N° LV": rec["reference"],
                "DATE ÉVACUATION": f"{jour:%d/%m/%Y}",
                "CAMION": str(et.get("camion") or "").strip(), "CHAUFFEUR": str(et.get("chauffeur") or "").strip(),
                "DESTINATION": "" if rupture else str(et.get("destination") or "").strip(),
                "SITE": str(et.get("destination") or "").strip() if rupture else "", "DF10": b.get("df10") or "",
                "SÉQUENCE": b.get("sequence") or "", "ESSENCE": b.get("essence") or "",
                "VOLUME": float(b.get("volume") or 0), "TITRE": b.get("titre") or "",
                "REMORQUE": str(et.get("remorque") or "").strip(), "TÉLÉPHONE": str(et.get("telephone") or "").strip(),
                "OBSERVATION": str(et.get("observation") or "").strip(),
                "ÉTABLI PAR": rec.get("nom_affiche") or "",
                "ÉMIS LE": rec["cree_le"].astimezone(FUSEAU).strftime("%d/%m/%Y %H:%M"),
            }
    rows = sorted(par_code.values(), key=lambda r: (r["DATE ÉVACUATION"][6:] + r["DATE ÉVACUATION"][3:5] + r["DATE ÉVACUATION"][:2],
                                                    r["OPÉRATION"] != "RUPTURE", r["N° LV"], r["CODE BARRE"]))
    return rows, {"chargements": len(refs), "billes": len(rows), "volume": sum(r["VOLUME"] for r in rows),
                  "sans_cb": sans_cb, "remplacees": remplacees,
                  "rupture": sum(1 for r in rows if r["OPÉRATION"] == "RUPTURE"), "negoce": sum(1 for r in rows if r["OPÉRATION"] == "NEGOCE")}


def csv_chargements(rows: list[dict]) -> bytes:
    import csv as _csv
    flux = io.StringIO()
    w = _csv.writer(flux, delimiter=";", lineterminator="\r\n")
    w.writerow(COLS_FICHIER_CHARGEMENTS)
    for r in rows:
        w.writerow([f"{r[c]:.3f}".replace(".", ",") if c == "VOLUME" else r[c] for c in COLS_FICHIER_CHARGEMENTS])
    return flux.getvalue().encode("utf-8-sig")


def panneau_fichier_chargements():
    """Historique : fichier unique des chargements d'une période (pour mettre à jour l'app)."""
    with st.expander("Fichier des chargements", expanded=False, icon=":material/download:"):
        st.caption("Choisissez la période : un seul fichier regroupe les chargements « Forêt → Rupture » et « Négoce » (opération, N° LV, "
                   "date, camion, chauffeur, site ou destination, une ligne par bille). Dans l'app : bouton **Chargements mobile**.")
        op = seg("Opération", OPERATIONS_FICHIER, default="Tous", key="hx_fich_op", label_visibility="collapsed")
        du, au = choix_periode("hx_fich")
        try:
            rows, st_ = chargements_periode(du, au, op)
        except Exception:
            journal.exception("Fichier des chargements indisponible")
            st.markdown('<div class="m4-vide">Historique indisponible (table mobile_exports absente ?).</div>', unsafe_allow_html=True)
            return
        if not rows:
            st.markdown(f'<div class="m4-vide">Aucun chargement {e(texte_periode(du, au))}.</div>', unsafe_allow_html=True)
            return
        st.markdown('<div class="m4-kpis">' + kpi("Billes", str(st_["billes"]), "", "#2D6A4F", sous=f'{st_["chargements"]} chargement(s) · {st_["rupture"]} vers rupture · {st_["negoce"]} négoce')
                    + kpi("Volume", fr(st_["volume"]), "m³", "#52B788")
                    + '</div>', unsafe_allow_html=True)
        if st_["sans_cb"]:
            st.warning(f"{st_['sans_cb']} bille(s) sans code barre : absentes du fichier.")
        if st_["remplacees"]:
            st.info(f"{st_['remplacees']} bille(s) présente(s) dans plusieurs chargements : le plus récent est retenu.")
        nom = "chargements_" + {"Forêt → Rupture": "rupture_", "Négoce": "negoce_"}.get(op, "") + (f"{du:%Y%m%d}" if du else "debut") + "_" + (f"{au:%Y%m%d}" if au else "ce_jour") + ".csv"
        st.download_button("Télécharger le fichier des chargements", csv_chargements(rows), file_name=nom, mime="text/csv",
                           type="primary", width="stretch", icon=":material/table_view:", key="hx_fich_dl",
                           on_click=noter, args=(st.session_state["utilisateur"]["id"], "chargement", f"fichier {nom}"))


def vue_historique():
    st.markdown("Tous les exports émis depuis cette page : cherchez une **bille** (DF10, séquence, code barre), une "
                "**référence**, un chauffeur ou un contrat.")
    if role_actuel() == "tracabilite":
        panneau_fichier_chargements()
    cle = st.text_input("Recherche", key="hx_q", placeholder="Ex. 53629/10/1 · 00813 · EV-2026… · contrat", label_visibility="collapsed").strip()
    genre = seg("Genre", ["Tous", "Forêt → Rupture", "Négoce", "Parc usine"], default="Tous", key="hx_genre", label_visibility="collapsed")
    w, p = ["TRUE"], []
    if genre == "Forêt → Rupture":
        w.append("genre = 'foret'")
    elif genre == "Négoce":
        w.append("genre = 'camion'")
    elif genre == "Parc usine":
        w.append("genre = 'usine'")
    if cle:
        w.append("(recherche LIKE %s OR reference ILIKE %s OR chauffeur ILIKE %s OR contrat ILIKE %s OR destination ILIKE %s OR camion ILIKE %s)")
        p += [f"%{cle.lower()}%"] + [f"%{cle}%"] * 5
    try:
        lignes = requete("SELECT reference, genre, to_char(cree_le AT TIME ZONE 'Africa/Douala','DD/MM/YYYY HH24:MI') AS le, "
                         "nom_affiche, role, contrat, destination, chauffeur, camion, essence, nb, volume, billes, statut, donnees "
                         f"FROM public.mobile_exports WHERE {' AND '.join(w)} ORDER BY cree_le DESC LIMIT 30", p)
    except Exception:
        st.markdown('<div class="m4-vide">L\'historique n\'est pas encore activé : lancez « gerer_utilisateurs_mobile.py preparer » '
                    'sur le PC.</div>', unsafe_allow_html=True)
        return
    if not lignes:
        st.markdown('<div class="m4-vide">Aucun export trouvé.</div>', unsafe_allow_html=True)
        return
    st.caption(f"{len(lignes)} export(s) — les 30 plus récents correspondant à la recherche.")
    peut_statut = role_actuel() == "tracabilite"
    for r in lignes:
        icone = {"camion": "🚚", "foret": "🌲"}.get(r["genre"], "🏭")
        cible = r["destination"] if r["genre"] in ("camion", "foret") else r["contrat"]
        with st.expander(f"{icone} {r['reference']} · {r['nb']} billes · {r['statut']}"):
            st.markdown(f'<div class="m4-fiche-s">{e(r["le"])} · par <b>{e(r["nom_affiche"])}</b> · {fr(r["volume"])} m³'
                        + (f' · {e(cible)}' if cible else "") + (f' · {e(r["chauffeur"])} {e(r["camion"])}' if r["genre"] in ("camion", "foret") else "")
                        + "</div>", unsafe_allow_html=True)
            st.markdown('<div style="font-size:.78rem;line-height:1.6">' + ", ".join(e(d) for d in r["billes"]) + "</div>", unsafe_allow_html=True)
            d = r["donnees"] or {}
            try:
                if r["genre"] in ("camion", "foret") and d.get("en_tete") and d.get("billes"):
                    bl = _billes_recues(d["billes"])
                    pdf_fn = chargement_foret.pdf_bordereau_foret if r["genre"] == "foret" else chargement.pdf_bordereau
                    st.download_button("Réimprimer le bordereau PDF", pdf_fn(d["en_tete"], bl), file_name=f"{r['reference']}.pdf",
                                       mime="application/pdf", width="stretch", key=f"hx_pdf_{r['reference']}", icon=":material/picture_as_pdf:")
                    st.download_button("Réexporter le CSV", chargement.csv_bordereau(d["en_tete"], bl), file_name=f"{r['reference']}.csv",
                                       mime="text/csv", width="stretch", key=f"hx_csv_{r['reference']}", icon=":material/table_view:")
                    st.download_button("Réexporter la LV", csv_lv(bl), file_name=f"{r['reference']}_LV.csv", mime="text/csv",
                                       width="stretch", key=f"hx_lv_{r['reference']}", icon=":material/barcode:")
                elif r["genre"] == "usine" and d.get("billes"):
                    st.download_button("Réexporter le CSV", chargement.csv_usine(_billes_recues(d["billes"]), r["essence"] or ""),
                                       file_name=f"{_slug(r['contrat'] or 'contrat')}_{r['reference']}.csv", mime="text/csv", width="stretch",
                                       key=f"hx_csv_{r['reference']}", icon=":material/table_view:")
            except Exception:
                journal.exception("Réimpression impossible")
                st.caption("Réimpression indisponible pour cet export.")
            if peut_statut:
                choix = st.segmented_control("Statut", STATUTS, default=r["statut"], key=f"hx_st_{r['reference']}", label_visibility="collapsed")
                if choix and choix != r["statut"]:
                    maj_statut(r["reference"], choix)
                    st.rerun()
            else:
                st.caption(f"Statut : {r['statut']}")


# ---------------------------------------------------------------------------
# Chargement Parc Forêt → Parc de rupture : sans limite de billes, bordereau multi-pages
# ---------------------------------------------------------------------------
MAX_LIGNES_FILTRE = 400     # billes listées d'un coup dans le filtre ; « Ajouter tout le filtre » les prend toutes


def billes_parc_foret() -> list[dict]:
    """Billes au Parc Forêt (hors Abandon), prêtes à partir vers un Parc de rupture."""
    lst = q("SELECT TRIM(b.df10) AS df10, NULLIF(TRIM(b.sequence),'') AS sequence, NULLIF(TRIM(b.code_barre),'') AS code_barre, "
            "b.longueur, b.dgb, b.dpb, COALESCE(b.volume,0) AS volume, UPPER(TRIM(COALESCE(b.essence,''))) AS essence, "
            "TRIM(COALESCE(b.titre,'')) AS titre, TRIM(COALESCE(b.statut,'')) AS statut, TRIM(COALESCE(b.situation,'')) AS situation "
            "FROM billonnage b "
            "WHERE UPPER(TRIM(COALESCE(b.situation,''))) IN ('PARC FORÊT', 'PARC FORET') "
            f"AND {NON_ABANDON} AND TRIM(COALESCE(b.df10,'')) <> ''")
    return sorted(lst, key=lambda b: cle_df10(b["df10"]))


def valeurs_transport(colonne: str) -> list[str]:
    """Camions ou chauffeurs déjà connus (billonnage + chargements mobiles), sans doublon, pour la saisie assistée."""
    assert colonne in ("camion", "chauffeur")
    vus = {}
    try:
        if q("SELECT 1 FROM information_schema.columns WHERE table_schema = 'public' AND table_name = 'billonnage' "
             f"AND column_name = '{colonne}'"):
            for r in q(f"SELECT DISTINCT TRIM({colonne}) AS v FROM billonnage WHERE TRIM(COALESCE({colonne},'')) <> ''"):
                vus.setdefault(" ".join(str(r["v"]).split()).upper(), " ".join(str(r["v"]).split()))
    except Exception:
        pass
    try:
        for r in requete(f"SELECT DISTINCT TRIM({colonne}) AS v FROM public.mobile_exports WHERE TRIM(COALESCE({colonne},'')) <> ''"):
            vus.setdefault(" ".join(str(r["v"]).split()).upper(), " ".join(str(r["v"]).split()))
    except Exception:
        pass
    return sorted(vus.values(), key=str.upper)


def tableau_billes_foret(billes: list[dict], max_lignes: int | None = None) -> str:
    """Aperçu des billes : Essence, Code barre, Séquence, DGB, DPB, Longueur, Volume, Statut, Situation (alignement de la saisie)."""
    lot = billes if max_lignes is None else billes[:max_lignes]
    corps = "".join(
        f'<tr><td>{e(b["essence"] or "—")}</td><td><b>{e(b["code_barre"] or "—")}</b></td><td>{e(b["sequence"] or "")}</td>'
        f'<td>{e(chargement._dim(b["dgb"]))}</td><td>{e(chargement._dim(b["dpb"]))}</td>'
        f'<td>{"" if b["longueur"] is None else fr(b["longueur"], 2)}</td><td><b>{fr(b["volume"])}</b></td>'
        f'<td>{icone_statut(b.get("statut"))}</td><td>{e(b.get("situation") or "")}</td></tr>' for b in lot)
    tete = "".join(f"<th>{h}</th>" for h in ["Essence", "Code barre", "Séquence", "DGB", "DPB", "Long.", "m³", "Statut", "Situation"])
    css = ('<style>.m4-stk th,.m4-stk td{padding:.4rem .16rem !important;font-size:.58rem !important;letter-spacing:0 !important;'
           'text-align:left !important;white-space:nowrap}.m4-stk td:nth-child(8),.m4-stk th:nth-child(8){text-align:center !important}</style>')
    return css + f'<div class="m4-mx-wrap"><table class="m4-mx m4-chg m4-stk"><thead><tr>{tete}</tr></thead><tbody>{corps}</tbody></table></div>'


def csv_stock_foret(billes: list[dict]) -> bytes:
    """CSV du stock Parc Forêt filtré (colonnes de l'aperçu, volumes à 3 décimales)."""
    def c(v):
        return '"' + str(v if v is not None else "").replace('"', '""') + '"'
    lig = [";".join(c(h) for h in ["ESSENCE", "CODE BARRE", "SÉQUENCE", "DF10", "TITRE", "DGB", "DPB", "LONGUEUR", "VOLUME", "STATUT", "SITUATION"])]
    for b in billes:
        lig.append(";".join(c(v) for v in [b["essence"], b["code_barre"], b["sequence"], b["df10"], b["titre"], chargement._dim(b["dgb"]),
                                           chargement._dim(b["dpb"]), "" if b["longueur"] is None else fr(b["longueur"], 2),
                                           fr(b["volume"]).replace("\u202f", "").replace("\xa0", "").replace(" ", ""),
                                           b.get("statut") or "", b.get("situation") or ""]))
    return ("\r\n".join(lig) + "\r\n").encode("utf-8-sig")


def _fo_ajouter_codes():
    """Callback : ajoute à la liste les DF10 / codes-barres / séquences collés (1102 → toutes les séquences finissant par -01102)."""
    par_cle = st.session_state.get("_fo_index", {})
    par_suffixe = st.session_state.get("_fo_suffixes", {})
    sel = st.session_state.setdefault("fo_sel", [])
    inconnus, doublons, multi = [], 0, []
    for jeton in _jetons(st.session_state.get("fo_coll", "")):
        b = par_cle.get(jeton.upper())
        if b is not None:
            trouvees = [b]
        elif jeton.isdigit():
            trouvees = par_suffixe.get(jeton.lstrip("0") or "0", [])
            if len(trouvees) > 1:
                multi.append((jeton, len(trouvees)))
        else:
            trouvees = []
        if not trouvees:
            inconnus.append(jeton)
        for t in trouvees:
            if t["df10"] in sel:
                doublons += 1
            else:
                sel.append(t["df10"])
    st.session_state["fo_msg"] = (inconnus, doublons, multi)
    st.session_state["fo_coll"] = ""


def _fo_ajouter_lignes(tous: bool):
    sel = st.session_state.setdefault("fo_sel", [])
    vue = st.session_state.get("_fo_vue", [])
    if tous:
        choisis = st.session_state.get("_fo_vue_tout", vue)
    else:
        idx = (st.session_state.get(f"fo_tab_{st.session_state.get('fo_gen', 0)}") or {}).get("selection", {}).get("rows", [])
        choisis = [vue[i] for i in idx if i < len(vue)]
    for d in choisis:
        if d not in sel:
            sel.append(d)
    st.session_state["fo_gen"] = st.session_state.get("fo_gen", 0) + 1     # nouvelle clé : la sélection du tableau repart à zéro


def _fo_retirer():
    sel = st.session_state.setdefault("fo_sel", [])
    idx = (st.session_state.get(f"fo_sel_tab_{st.session_state.get('fo_gen', 0)}") or {}).get("selection", {}).get("rows", [])
    a_retirer = {sel[i] for i in idx if i < len(sel)}
    st.session_state["fo_sel"] = [d for d in sel if d not in a_retirer]
    st.session_state["fo_gen"] = st.session_state.get("fo_gen", 0) + 1


def _fo_retirer_codes():
    """Callback : retire de la liste les billes désignées par DF10 / code barre / séquence (courte ou complète)."""
    sel = st.session_state.setdefault("fo_sel", [])
    par_df10 = st.session_state.get("_fo_par_df10", {})
    a_retirer, absents = set(), []
    for jeton in _jetons(st.session_state.get("fo_ret_coll", "")):
        j = jeton.upper()
        trouvees = []
        for d in sel:
            b = par_df10.get(d)
            if not b:
                continue
            seq = (b["sequence"] or "").strip().upper()
            fin = re.split(r"[-/\s]+", seq)[-1] if seq else ""
            if j in (d.upper(), (b["code_barre"] or "").upper(), seq) or (jeton.isdigit() and fin.isdigit() and (fin.lstrip("0") or "0") == (jeton.lstrip("0") or "0")):
                trouvees.append(d)
        if trouvees:
            a_retirer.update(trouvees)
        else:
            absents.append(jeton)
    st.session_state["fo_sel"] = [d for d in sel if d not in a_retirer]
    st.session_state["fo_msg_ret"] = (len(a_retirer), absents)
    st.session_state["fo_ret_coll"] = ""
    st.session_state["fo_gen"] = st.session_state.get("fo_gen", 0) + 1


def _fo_vider():
    st.session_state["fo_sel"] = []
    st.session_state["fo_gen"] = st.session_state.get("fo_gen", 0) + 1


def vue_chargement_foret():
    st.markdown("Chargement **Parc Forêt → Parc de rupture**, **sans limite de billes** : composez la liste (onglet « Stock » ou « LV Forêt »), "
                "indiquez le transport et le site de destination. L'onglet « Stock » sert aussi à **consulter le stock du Parc Forêt**. Vous obtenez un **bordereau PDF** (plusieurs pages si besoin), "
                "un **CSV** et le **fichier LV**. Rien n'est modifié dans la base : la mise à jour se fait ensuite dans l'app.")
    dispo = billes_parc_foret()
    if not dispo:
        st.markdown('<div class="m4-vide">Aucune bille disponible au Parc Forêt.</div>', unsafe_allow_html=True)
        return
    par_df10 = {b["df10"]: b for b in dispo}     # toute la liste du chargement, quel que soit le titre filtré
    st.session_state["_fo_par_df10"] = par_df10
    titres = sorted({b["titre"] for b in dispo if b["titre"]})
    f_titre = st.selectbox("Titre", ["Tous"] + titres, key="fo_f_titre")
    dispo_t = [b for b in dispo if f_titre == "Tous" or b["titre"] == f_titre]    # le filtre Titre s'applique à Stock et LV Forêt
    par_cle = {}
    for b in dispo_t:
        par_cle[b["df10"].upper()] = b
        if b["code_barre"]:
            par_cle.setdefault(b["code_barre"].upper(), b)
    par_suffixe = {}      # n° de séquence saisi court (1102, 10, 213…) -> toutes les billes dont la séquence finit par ce numéro
    for b in dispo_t:
        seq = (b["sequence"] or "").strip().upper()
        if seq:
            par_cle.setdefault(seq, b)
            fin = re.split(r"[-/\s]+", seq)[-1]
            if fin.isdigit():
                par_suffixe.setdefault(fin.lstrip("0") or "0", []).append(b)
    st.session_state["_fo_index"] = par_cle
    st.session_state["_fo_suffixes"] = par_suffixe
    sel = [d for d in st.session_state.setdefault("fo_sel", []) if d in par_df10]   # une bille évacuée entre-temps disparaît
    st.session_state["fo_sel"] = sel
    if sel:
        vol_draft = sum(float(par_df10[d]["volume"]) for d in sel)
        st.markdown(f'<div class="m4-draft-banner"><span>💾 Brouillon en cours : {len(sel)} bille(s) mémorisée(s)</span>'
                    f'<span>{fr(vol_draft)} m³</span></div>', unsafe_allow_html=True)

    st.markdown(f'<div class="m4-sec" style="margin-top:.6rem">1 · Billes <span style="text-transform:none;letter-spacing:0">'
                f'({len(dispo_t)} disponibles au Parc Forêt{"" if f_titre == "Tous" else " · titre " + e(f_titre)})</span></div>', unsafe_allow_html=True)
    mode = seg("Sélection", ["Stock", "LV Forêt"], default="Stock", key="fo_mode", label_visibility="collapsed")
    if mode == "LV Forêt":
        widget_scan_codebarre("fo_coll", "cam_fo_lv")
        st.text_area("DF10 / codes-barres / séquences (un par ligne ou séparés par un espace)", key="fo_coll", height=110,
                     placeholder="Ex. 53629/10/1  1102  213")
        st.caption("Une séquence peut être saisie sans zéros : 1102 trouve « …-01102 », 10 trouve « …-00010 », 213 trouve « …-00213 ». "
                   "Si plusieurs billes se terminent ainsi, elles sont toutes ajoutées.")
        st.button("Ajouter à la liste", key="fo_btn_coll", on_click=_fo_ajouter_codes, type="primary", width="stretch")
        msg = st.session_state.get("fo_msg")
        if msg:
            inc, dbl, multi = msg
            for jeton, n_ in multi:
                st.info(f"« {jeton} » : {n_} séquences se terminent ainsi, toutes ont été ajoutées — vérifiez l'aperçu.")
            if inc:
                st.warning("Introuvable (DF10, code barre ou séquence) ou indisponible au Parc Forêt (déjà évacuée, abandon, autre situation" + ("" if f_titre == "Tous" else ", autre titre que " + f_titre) + ") : " + ", ".join(inc[:10])
                           + ("…" if len(inc) > 10 else ""))
            if dbl:
                st.info(f"{dbl} doublon(s) ignoré(s).")
    else:
        f_txt = st.text_input("DF10 contient", key="fo_f_txt", placeholder="Ex. 53629/10 (une grume) ou 53629").strip().upper()
        f_cb = st.text_input("Code barre / séquence contient", key="fo_f_cb", placeholder="Ex. 12034").strip().upper()
        tout = [b for b in dispo_t if (not f_txt or f_txt in b["df10"].upper())
                and (not f_cb or f_cb in (b["code_barre"] or "").upper() or f_cb in (b["sequence"] or "").upper())]
        vue = [b for b in tout if b["df10"] not in sel]
        st.session_state["_fo_vue"] = [b["df10"] for b in vue[:MAX_LIGNES_FILTRE]]
        st.session_state["_fo_vue_tout"] = [b["df10"] for b in vue]
        if not tout:
            st.caption("Aucune bille du Parc Forêt ne correspond à ce filtre.")
        else:
            vol = sum(float(b["volume"]) for b in tout)
            st.markdown('<div class="m4-sec">Stock Parc Forêt</div><div class="m4-kpis">'
                        + kpi("Billes", str(len(tout)), "", "#2D6A4F", sous=f"sur {len(dispo_t)} au parc")
                        + kpi("Volume", fr(vol), "m³", "#52B788") + '</div>', unsafe_allow_html=True)
            par_ess = {}
            for b in tout:
                n_, v_ = par_ess.get(b["essence"] or "—", (0, 0.0))
                par_ess[b["essence"] or "—"] = (n_ + 1, v_ + float(b["volume"]))
            rec_ess = pd.DataFrame([{"Essence": k, "Billes": n_, "m³": v_} for k, (n_, v_) in sorted(par_ess.items(), key=lambda x: -x[1][1])])
            st.dataframe(rec_ess, hide_index=True, width="stretch", height=min(260, 38 + 35 * len(rec_ess)),
                         column_config={"m³": st.column_config.NumberColumn(format="%.3f")})
            nb_aff = min(len(tout), MAX_LIGNES_FILTRE)
            st.caption(f"Billes du filtre" + (f" — les {MAX_LIGNES_FILTRE} premières sur {len(tout)} (le CSV contient tout)" if len(tout) > MAX_LIGNES_FILTRE else "") + " :")
            st.markdown(tableau_billes_foret(tout, MAX_LIGNES_FILTRE), unsafe_allow_html=True)
            st.download_button("Télécharger le stock filtré (CSV)", csv_stock_foret(tout), file_name="stock_parc_foret.csv", mime="text/csv",
                               width="stretch", icon=":material/table_view:", key="fo_csv_stock")
            if vue:
                with st.expander("Préparer un chargement avec ces billes"):
                    st.caption("Facultatif : choisissez des billes précises, ou prenez tout le filtre, pour les ajouter à la liste du chargement.")
                    nb_sel = min(len(vue), MAX_LIGNES_FILTRE)
                    df = pd.DataFrame([{"Essence": b["essence"], "Code barre": b["code_barre"] or "", "Séquence": b["sequence"] or "",
                                        "DF10": b["df10"], "m³": float(b["volume"])} for b in vue[:nb_sel]])
                    st.dataframe(df, hide_index=True, width="stretch", height=min(320, 38 + 35 * nb_sel),
                                 key=f"fo_tab_{st.session_state.get('fo_gen', 0)}", on_select="rerun", selection_mode="multi-row",
                                 column_config={"m³": st.column_config.NumberColumn(format="%.3f")})
                    n_choisies = len((st.session_state.get(f"fo_tab_{st.session_state.get('fo_gen', 0)}") or {}).get("selection", {}).get("rows", []))
                    b1, b2 = st.columns(2)
                    b1.button(f"Ajouter les {n_choisies} choisie(s)" if n_choisies else "Ajouter les choisies", key="fo_btn_sel",
                              on_click=_fo_ajouter_lignes, args=(False,), disabled=not n_choisies, width="stretch")
                    b2.button(f"Ajouter tout le filtre ({len(vue)})", key="fo_btn_tout",
                              on_click=_fo_ajouter_lignes, args=(True,), type="primary", width="stretch")
                    if len(vue) > MAX_LIGNES_FILTRE:
                        st.caption(f"« Ajouter tout le filtre » prend les {len(vue)} billes, pas seulement les {MAX_LIGNES_FILTRE} listées.")

    billes = [par_df10[d] for d in sel]
    if billes:
        total = sum(float(b["volume"]) for b in billes)
        st.markdown('<div class="m4-sec">Liste du chargement — vérifiez</div>', unsafe_allow_html=True)
        st.markdown('<div class="m4-kpis">' + kpi("Billes", str(len(billes)), "", "#2D6A4F", sous=f"{len({b['titre'] for b in billes})} titre(s)")
                    + kpi("Volume", fr(total), "m³", "#52B788") + '</div>', unsafe_allow_html=True)
        dfs = pd.DataFrame([{"Essence": b["essence"] or "—", "Code barre": b["code_barre"] or "", "Séquence": b["sequence"] or "",
                             "DF10": b["df10"], "DGB": chargement._dim(b["dgb"]), "DPB": chargement._dim(b["dpb"]),
                             "Long.": "" if b["longueur"] is None else fr(b["longueur"], 2), "m³": float(b["volume"]),
                             "Statut": icone_statut(b.get("statut")), "Situation": b.get("situation") or ""} for b in billes])
        st.caption("Cochez une ou plusieurs lignes pour les retirer · touchez un titre de colonne pour trier.")
        st.dataframe(dfs, hide_index=True, width="stretch", height=min(460, 40 + 35 * len(billes)),
                     key=f"fo_sel_tab_{st.session_state.get('fo_gen', 0)}", on_select="rerun", selection_mode="multi-row",
                     column_config={"m³": st.column_config.NumberColumn(format="%.3f", width="small"),
                                    "Statut": st.column_config.TextColumn(width="small"),
                                    "DGB": st.column_config.TextColumn(width="small"), "DPB": st.column_config.TextColumn(width="small"),
                                    "Long.": st.column_config.TextColumn(width="small")})
        n_ret = len((st.session_state.get(f"fo_sel_tab_{st.session_state.get('fo_gen', 0)}") or {}).get("selection", {}).get("rows", []))
        r1, r2 = st.columns(2)
        r1.button(f"Retirer les {n_ret} cochée(s)" if n_ret else "Retirer les cochées", key="fo_btn_ret", on_click=_fo_retirer,
                  disabled=not n_ret, width="stretch", icon=":material/remove_circle_outline:")
        r2.button("Vider la liste", key="fo_btn_vider", on_click=_fo_vider, width="stretch", icon=":material/delete_sweep:")
        st.text_input("Retirer par code", key="fo_ret_coll", on_change=_fo_retirer_codes, placeholder="DF10, code barre ou séquence (ex. 1102) — Entrée pour retirer",
                      help="Retire de la liste les billes correspondantes ; une séquence courte retire toutes celles qui se terminent ainsi.")
        msg_r = st.session_state.pop("fo_msg_ret", None)
        if msg_r:
            if msg_r[0]:
                st.success(f"{msg_r[0]} bille(s) retirée(s).")
            if msg_r[1]:
                st.warning("Absent de la liste : " + ", ".join(msg_r[1][:10]))
        st.download_button("Exporter la liste (CSV)", csv_stock_foret(billes), file_name="liste_chargement_foret.csv", mime="text/csv",
                           width="stretch", icon=":material/table_view:", key="fo_csv_liste")
        avertir_deja([b["df10"] for b in billes], None)
        sans_cb = sum(1 for b in billes if not b.get("code_barre"))
        if sans_cb:
            st.warning(f"{sans_cb} bille(s) sans code barre : absente(s) de la LV et du fichier des chargements "
                       "(l'app ne pourra pas les traiter).")

    st.markdown('<div class="m4-sec">2 · Transport</div>', unsafe_allow_html=True)
    lv_nom = st.text_input("N° LV (nom d'enregistrement) *", key="fo_lv_nom", max_chars=60, placeholder="Ex. LV-2026-0123",
                           help="Ce nom devient le N° LV des billes dans l'app, et le nom des fichiers.").strip()
    chauffeur = (st.selectbox("Chauffeur *", valeurs_transport("chauffeur"), key="fo_chauf", index=None, accept_new_options=True,
                              placeholder="Tapez quelques lettres (ex. Serge) : les chauffeurs connus sont proposés") or "").strip()
    camion = (st.selectbox("Camion (immatriculation) *", valeurs_transport("camion"), key="fo_camion", index=None, accept_new_options=True,
                           placeholder="Tapez une partie du numéro (ex. 400) : les camions connus sont proposés") or "").strip()
    sites = liste_sites()
    AUTRE = "Autre site…"
    choix_site = st.selectbox("Site du Parc de rupture (destination) *", sites + [AUTRE] if sites else [AUTRE], key="fo_site_sel",
                              index=None, placeholder="Choisir le site")
    site = ""
    if choix_site == AUTRE:
        site = st.text_input("Nom du site *", key="fo_site_txt", max_chars=60, placeholder="Ex. BATOURI").strip().upper()
    elif choix_site:
        site = choix_site
    jour = st.date_input("Date d'évacuation", value=datetime.now(FUSEAU).date(), key="fo_date", format="DD/MM/YYYY")
    obs = st.text_input("Observation", key="fo_obs", max_chars=120)
    manque = [n for n, v in (("N° LV", lv_nom), ("chauffeur", chauffeur), ("camion", camion), ("site de destination", site))
              if not v.strip()]
    st.markdown('<div class="m4-sec">3 · Documents</div>', unsafe_allow_html=True)
    if not billes or manque:
        st.caption("Ajoutez au moins une bille et renseignez " + (", ".join(manque) if manque else "le transport") + "."
                   if billes or manque else "Ajoutez au moins une bille.")
        return
    codes = [b["df10"] for b in billes]
    if re.search(r'[\\/:*?"<>|]', lv_nom):
        st.error("Le N° LV ne peut pas contenir les caractères suivants : / \\ : * ? < > | et les guillemets.")
        return
    try:     # une référence = un seul chargement : un nom déjà pris par une autre liste ferait perdre cet export
        pris = requete("SELECT genre, statut, billes FROM public.mobile_exports WHERE reference = %s", (lv_nom,))
    except Exception:
        pris = []
    if pris and (pris[0]["genre"] != "foret" or set(pris[0]["billes"] or []) != set(codes)):
        st.error(f"Le N° LV « {lv_nom} » est déjà utilisé par un autre chargement. Choisissez un autre nom.")
        return
    empreinte = "|".join(sorted(codes))
    memo = st.session_state.get("fo_stamp")
    if not memo or memo[0] != empreinte:
        memo = (empreinte, datetime.now(FUSEAU))
        st.session_state["fo_stamp"] = memo
    stamp = memo[1]
    en_tete = {"reference": lv_nom, "date": f"{jour:%Y-%m-%d}",
               "date_texte": f"{jour:%d/%m/%Y} à {stamp:%H:%M}", "chauffeur": chauffeur.strip(), "telephone": "",
               "camion": camion.strip().upper(), "remorque": "", "destination": site.strip().upper(),
               "etabli_par": st.session_state["utilisateur"]["nom"], "observation": obs.strip()}
    nom = en_tete["reference"]
    pdf = chargement_foret.pdf_bordereau_foret(en_tete, billes)
    csv_ = chargement.csv_bordereau(en_tete, billes)
    rec = preparer_export("foret", nom, billes, sum(float(b["volume"]) for b in billes), destination=en_tete["destination"],
                          chauffeur=en_tete["chauffeur"], camion=en_tete["camion"], donnees={"en_tete": en_tete, "billes": billes})
    st.markdown(f'<div class="m4-fiche-s">Référence : <b>{e(nom)}</b></div>', unsafe_allow_html=True)
    st.download_button("Bordereau PDF", pdf, file_name=f"{nom}.pdf", mime="application/pdf", type="primary",
                       width="stretch", icon=":material/picture_as_pdf:", key="fo_pdf", on_click=noter_bordereau, args=(nom, "pdf", rec))
    st.download_button("Fichier CSV", csv_, file_name=f"{nom}.csv", mime="text/csv",
                       width="stretch", icon=":material/table_view:", key="fo_csv", on_click=noter_bordereau, args=(nom, "csv", rec))
    st.download_button("Fichier LV", csv_lv(billes), file_name=f"{nom}_LV.csv", mime="text/csv",
                       width="stretch", icon=":material/barcode:", key="fo_lv", on_click=noter_bordereau, args=(nom, "lv", rec))
    st.caption("Le N° LV saisi sert de référence et de nom de fichier ; chaque export est gardé dans l'onglet « Historique ». "
               "Le fichier des chargements d'une période (Historique) met ensuite à jour l'app : bille en Parc de rupture, "
               "site et N° LV renseignés.")


# ---------------------------------------------------------------------------
# Contrôle de chargement : billes scannées sur le camion ↔ contenu du LV
# ---------------------------------------------------------------------------
@st.cache_data(ttl=60, show_spinner=False)
def _infos_billes(codes: tuple) -> dict:
    """Pour les codes scannés hors LV : où se trouve réellement la bille (clé = code saisi en majuscules)."""
    if not codes:
        return {}
    lignes = q("SELECT b.df10, b.code_barre, UPPER(TRIM(b.essence)) AS essence, b.volume, b.situation, b.numero_lv FROM billonnage b "
               "WHERE UPPER(TRIM(b.df10)) = ANY(%s) OR UPPER(TRIM(b.code_barre)) = ANY(%s)", [list(codes), list(codes)])
    res = {}
    for r in lignes:
        for c in (str(r["df10"] or "").strip().upper(), str(r["code_barre"] or "").strip().upper()):
            if c in codes:
                res[c] = r
    return res


def _vider_controle():
    st.session_state["ctl_scan"] = ""


def vue_controle_lv():
    st.markdown("Vérifiez ce qui est **réellement chargé** : scannez le LV, puis les billes sur le camion. "
                "L'écran signale les billes **manquantes** et celles **en trop**. Rien n'est modifié dans la base.")
    st.markdown('<div class="m4-sec" style="margin-top:.6rem">1 · LV à contrôler</div>', unsafe_allow_html=True)
    widget_scan_codebarre("ctl_lv", "cam_ctl_lv")
    st.text_area("N° LV ou code barre LV", key="ctl_lv", height=68, placeholder="Ex. 2177766")
    jl = _jetons(st.session_state.get("ctl_lv", ""))
    if not jl:
        st.markdown('<div class="m4-vide">Saisissez ou scannez le LV pour afficher son contenu.</div>', unsafe_allow_html=True)
        return
    attendues = _billes_du_lv(jl[0].upper())
    if not attendues:
        st.warning(f"LV « {jl[0]} » introuvable : vérifiez le numéro.")
        return
    num = next((str(r["numero_lv"]).strip() for r in attendues if str(r.get("numero_lv") or "").strip()), jl[0])
    camions = ", ".join(sorted({str(r["camion"]).strip() for r in attendues if str(r.get("camion") or "").strip()}))
    v_att = sum(float(r["volume"] or 0) for r in attendues)
    st.markdown(f'<div class="m4-fiche-t"><b>LV N° {e(num)}</b>{badge(str(len(attendues)) + " bille(s) attendue(s)", "neutral")}</div>'
                f'<div class="m4-fiche-s">{e(camions)}{" · " if camions else ""}{fr(v_att)} m³</div>', unsafe_allow_html=True)
    st.markdown('<div class="m4-sec">2 · Billes sur le camion</div>', unsafe_allow_html=True)
    widget_scan_codebarre("ctl_scan", "cam_ctl_bil")
    st.text_area("Billes scannées (DF10 ou code barre)", key="ctl_scan", height=110, placeholder="Scannez les billes une à une, ou collez la liste")
    st.button("Tout effacer", key="ctl_vider", on_click=_vider_controle, icon=":material/delete_sweep:", width="stretch")
    scannes = _jetons(st.session_state.get("ctl_scan", ""))
    if not scannes:
        st.markdown('<div class="m4-vide">Aucune bille scannée pour l\'instant.</div>', unsafe_allow_html=True)
        return
    par_code = {}
    for r in attendues:
        for c in (str(r["df10"] or "").strip().upper(), str(r["code_barre"] or "").strip().upper()):
            if c:
                par_code[c] = r
    trouvees, en_trop, doublons, vus = [], [], 0, set()
    for j in scannes:
        u = j.upper()
        r = par_code.get(u)
        cle = (r["df10"] if r else u)
        if cle in vus:
            doublons += 1
            continue
        vus.add(cle)
        (trouvees if r else en_trop).append(r if r else u)
    ids_ok = {r["df10"] for r in trouvees}
    manquantes = [r for r in attendues if r["df10"] not in ids_ok]
    ailleurs = _infos_billes(tuple(en_trop))
    n_att, n_ok = len(attendues), len(trouvees)
    if not manquantes and not en_trop:
        classe, titre = "ok", f"CONFORME · {n_ok} / {n_att} billes"
    elif en_trop:
        classe = "ko"
        titre = f"ÉCART · {len(en_trop)} bille(s) en trop" + (f" · {len(manquantes)} manquante(s)" if manquantes else "")
    else:
        classe, titre = "mid", f"INCOMPLET · {n_ok} / {n_att} · il manque {len(manquantes)} bille(s)"
    v_ok = sum(float(r["volume"] or 0) for r in trouvees)
    st.markdown(f'<div class="m4-ctl {classe}"><b>{e(titre)}</b><span>{fr(v_ok)} m³ sur {fr(v_att)} m³ · {datetime.now(FUSEAU):%d/%m/%Y %H:%M}</span></div>',
                unsafe_allow_html=True)
    st.markdown('<div class="m4-kpis">' + kpi("Attendues", str(n_att), "", "#6C8EAD") + kpi("Conformes", str(n_ok), "", "#2D6A4F") + '</div>'
                + '<div class="m4-kpis">' + kpi("Manquantes", str(len(manquantes)), "", "#C9822B" if manquantes else "#2D6A4F")
                + kpi("En trop", str(len(en_trop)), "", "#B94A44" if en_trop else "#2D6A4F") + '</div>', unsafe_allow_html=True)
    if doublons:
        st.caption(f"{doublons} scan(s) en double ignoré(s).")

    def tableau(rows_html: str, tete: str) -> str:
        return f'<div class="m4-lv-w"><table class="m4-lv-t"><thead><tr>{tete}</tr></thead><tbody>{rows_html}</tbody></table></div>'
    if en_trop:
        st.markdown('<div class="m4-sec">En trop : scannées mais absentes de ce LV</div>', unsafe_allow_html=True)
        lig = ""
        for c in en_trop:
            r = ailleurs.get(c)
            if r:
                lieu = f"LV {e(r['numero_lv'])}" if str(r.get("numero_lv") or "").strip() else "sans LV"
                lig += (f'<tr><td><b>{e(r["df10"])}</b></td><td>{e(str(r["essence"] or "")[:3])}</td><td>{fr(r["volume"])}</td>'
                        f'<td>📍 {e(r.get("situation") or "–")} · {lieu}</td></tr>')
            else:
                lig += f'<tr><td><b>{e(c)}</b></td><td></td><td></td><td>code inconnu dans la base</td></tr>'
        st.markdown(tableau(lig, "<th>Bille</th><th>Ess.</th><th>m³</th><th>Où elle se trouve</th>"), unsafe_allow_html=True)
    if manquantes:
        st.markdown('<div class="m4-sec">Manquantes : sur le LV, pas encore scannées</div>', unsafe_allow_html=True)
        lig = "".join(f'<tr><td><b>{e(r["df10"])}</b></td><td>{e(r["code_barre"] or "")}</td><td>{e(str(r["essence"] or "")[:3])}</td><td>{fr(r["volume"])}</td></tr>'
                      for r in manquantes)
        st.markdown(tableau(lig, "<th>Bille</th><th>CB</th><th>Ess.</th><th>m³</th>"), unsafe_allow_html=True)
    if trouvees:
        with st.expander(f"Conformes ({n_ok})", icon=":material/check_circle:"):
            lig = "".join(f'<tr><td><b>{e(r["df10"])}</b></td><td>{e(r["code_barre"] or "")}</td><td>{e(str(r["essence"] or "")[:3])}</td><td>{fr(r["volume"])}</td><td>✅</td></tr>'
                          for r in trouvees)
            st.markdown(tableau(lig, "<th>Bille</th><th>CB</th><th>Ess.</th><th>m³</th><th></th>"), unsafe_allow_html=True)


# ---------------------------------------------------------------------------
# Mode terrain (sans réseau) : fichier de données chiffré vers la page « Terrain » du téléphone, et retour des chargements
# ---------------------------------------------------------------------------
def _destinations_connues() -> list[str]:
    try:
        return [r["v"] for r in requete("SELECT DISTINCT TRIM(destination) AS v FROM public.mobile_exports "
                                        "WHERE TRIM(COALESCE(destination,'')) <> '' ORDER BY 1")]
    except Exception:
        return []


def _fabriquer_terrain(code: str) -> bytes:
    donnees = terrain.construire_donnees(q, genere_par=st.session_state["utilisateur"]["nom"], camions=valeurs_transport("camion"),
                                         chauffeurs=valeurs_transport("chauffeur"), destinations=_destinations_connues(),
                                         maintenant=datetime.now(),
                                         app_url=str(st.secrets.get("terrain", {}).get("app_url", "") or ""))
    return terrain.fabriquer_fichier(donnees, code)


def _controler_chargement_terrain(ch: dict) -> tuple[list[str], list[str]]:
    """(blocages, remarques) d'un chargement revenu du terrain, d'après l'état ACTUEL de la base."""
    remarques = []
    df10s = [b["df10"] for b in ch["billes"]]
    lignes = {str(r["df10"]).strip().upper(): r for r in q(
        "SELECT TRIM(df10) AS df10, TRIM(COALESCE(statut,'')) AS statut, TRIM(COALESCE(situation,'')) AS situation "
        "FROM billonnage WHERE UPPER(TRIM(df10)) = ANY(%s)", [[d.upper() for d in df10s]])}
    for d in df10s:
        r = lignes.get(d.upper())
        if r is None:
            remarques.append(f"{d} : absente de la base")
        elif r["statut"].upper() == "ABANDON":
            remarques.append(f"{d} : en abandon")
        elif "PARC DE RUPTURE" not in r["situation"].upper():
            remarques.append(f"{d} : situation actuelle « {r['situation'] or '—'} »")
    deja = deja_exportees(df10s, ch["reference"])
    for d, v in deja.items():
        remarques.append(f"{d} : déjà dans {v[0]} ({v[1]}, {v[2]})")
    return [], remarques


def vue_terrain():
    st.markdown("Le **mode terrain** fonctionne **sans réseau** sur le téléphone : scan des billes, traçabilité, composition "
                "des chargements et bordereau. Vous lui donnez ses données (fichier chiffré, valable "
                f"**{terrain.VALIDITE_JOURS} jours**) et vous récupérez les chargements qu'il a enregistrés.")
    url = str(st.secrets.get("terrain", {}).get("url", "") or "")
    if url:
        st.markdown(f'<div class="m4-fiche-s">Page terrain : <a href="{e(url)}" target="_blank">{e(url)}</a></div>', unsafe_allow_html=True)
    st.markdown('<div class="m4-sec">1 · Données pour le téléphone</div>', unsafe_allow_html=True)
    code = st.text_input("Code d'accès du fichier", type="password", key="tr_code", max_chars=60,
                         placeholder="6 caractères au moins : à communiquer aux utilisateurs du terrain")
    erreur = terrain.code_acces_valide(code) if code else None
    if erreur:
        st.warning(erreur)
    st.caption("Sans ce code, le fichier ne montre rien. Il contient abattage, billonnage, inventaire et production : "
               "les mêmes données pour tous les utilisateurs.")
    if st.button("Préparer le fichier terrain", type="primary", width="stretch", icon=":material/cloud_download:", key="tr_go",
                 disabled=not code or bool(erreur)):
        with st.spinner("Collecte et chiffrement…"):
            try:
                octets = _fabriquer_terrain(code)
                st.session_state["tr_fichier"] = (octets, datetime.now())
                noter(st.session_state["utilisateur"]["id"], "terrain", f"données · {len(octets) // 1024} Ko")
                _age_fichier_terrain.clear()
            except Exception:
                journal.exception("Fichier terrain")
                st.error("Préparation impossible pour le moment. Réessayez dans un instant.")
    prete = st.session_state.get("tr_fichier")
    if prete:
        octets, quand = prete
        limite = quand + timedelta(days=terrain.VALIDITE_JOURS)
        nom = terrain.nom_fichier(quand)
        st.download_button(f"Télécharger ({len(octets) / 1024 / 1024:.2f} Mo)", octets, file_name=nom,
                           mime="application/octet-stream", width="stretch", icon=":material/download:", key="tr_dl")
        bouton_partager_fichier(octets, nom, "application/octet-stream", "Mich4Track : données du mode terrain")
        st.caption(f"Valable jusqu'au {limite:%d/%m/%Y à %H:%M}. Passé ce délai, la page terrain refuse de s'ouvrir : "
                   "préparez-en un nouveau.")
    st.markdown('<div class="m4-sec" style="margin-top:1rem">2 · Chargements revenus du terrain</div>', unsafe_allow_html=True)
    f = st.file_uploader("Fichier de chargements envoyé par le téléphone", type=["json", terrain.EXTENSION_CHARGEMENTS],
                         key="tr_up")
    if f is None:
        st.caption("Sur le téléphone : onglet « Envois » → « Envoyer ». Le fichier arrive par WhatsApp ou e-mail.")
        return
    try:
        chargements, avert = terrain.lire_chargements(f.getvalue())
    except ValueError as exc:
        st.error(str(exc))
        return
    for a in avert:
        st.warning(a)
    if not chargements:
        return
    try:
        deja = {r["reference"] for r in requete("SELECT reference FROM public.mobile_exports WHERE reference = ANY(%s)",
                                                 ([c["reference"] for c in chargements],))}
    except Exception:
        deja = set()
    a_importer = []
    for ch in chargements:
        en = ch["en_tete"]
        with st.container(border=True):
            st.markdown(f'<div class="m4-fiche-t"><b>{e(ch["reference"])}</b>'
                        f'{badge("Déjà importé" if ch["reference"] in deja else "Nouveau", "neutral")}</div>'
                        f'<div class="m4-fiche-s">{e(en["camion"])} · {e(en["chauffeur"])} → {e(en["destination"])}<br>'
                        f'{ch["nb"]} bille(s) · {fr(ch["volume"])} m³ · {e(en["date_texte"] or en["date"])} · établi par {e(en["etabli_par"])}</div>',
                        unsafe_allow_html=True)
            if ch["reference"] in deja:
                continue
            _, remarques = _controler_chargement_terrain(ch)
            if remarques:
                st.warning("À vérifier : " + " · ".join(remarques[:8]) + (" …" if len(remarques) > 8 else ""))
            a_importer.append(ch)
    if a_importer and st.button(f"Importer {len(a_importer)} chargement(s) dans l'historique", type="primary", width="stretch",
                                icon=":material/inbox:", key="tr_imp"):
        for ch in a_importer:
            en = ch["en_tete"]
            rec = preparer_export("camion", ch["reference"], ch["billes"], ch["volume"], destination=en["destination"],
                                  chauffeur=en["chauffeur"], camion=en["camion"],
                                  donnees={"en_tete": en, "billes": ch["billes"], "origine": "terrain", "cree_le": ch["cree_le"]})
            enregistrer_export(rec)
            noter(st.session_state["utilisateur"]["id"], "terrain", f"import {ch['reference']}")
        st.success(f"{len(a_importer)} chargement(s) importé(s) : ils apparaissent dans « Historique ».")
        st.session_state.pop("tr_up", None)


def vue_chargement():
    mode = seg("Type de chargement", ["Rupture", "Négoce", "Usine", "Contrôle", "Terrain", "Historique"], default="Rupture", key="ch_mode",
               label_visibility="collapsed")
    if mode == "Historique":
        vue_historique()
    elif mode == "Terrain":
        vue_terrain()
    elif mode == "Rupture":
        vue_chargement_foret()
    elif mode == "Usine":
        vue_lot_usine()
    elif mode == "Contrôle":
        vue_controle_lv()
    else:
        vue_chargement_camion()


SEUIL_PROCHE = 0.90   # « proche de la limite » à partir de 90 % du permis
SQL_ALERTES = """
WITH ab AS (SELECT TRIM(COALESCE(titre,'')) AS t, UPPER(TRIM(essence)) AS e, COUNT(*) AS n, COALESCE(SUM(volume),0) AS v
            FROM abattage WHERE TRIM(COALESCE(essence,'')) <> '' GROUP BY 1, 2),
     pe AS (SELECT TRIM(titre) AS t, UPPER(TRIM(essence)) AS e, COALESCE(SUM(pied),0) AS pied, COALESCE(SUM(volume),0) AS vol
            FROM permis GROUP BY 1, 2)
SELECT COALESCE(pe.t, ab.t) AS titre, COALESCE(pe.e, ab.e) AS essence, COALESCE(pe.pied,0) AS pied, COALESCE(pe.vol,0) AS vol,
       COALESCE(ab.n,0) AS n, COALESCE(ab.v,0) AS v, (pe.t IS NULL) AS sans_permis
FROM pe FULL JOIN ab ON pe.t = ab.t AND pe.e = ab.e
"""


def charger_alertes(titres: list, essences: list) -> list[dict]:
    """Une alerte par (titre, essence) qui dépasse son permis en tiges et/ou en volume, ou s'en approche."""
    out = []
    for r in q(SQL_ALERTES):
        if titres and r["titre"] not in titres:
            continue
        if essences and r["essence"] not in essences:
            continue
        pied, vol, n, v = int(r["pied"]), float(r["vol"]), int(r["n"]), float(r["v"])
        dep_n, dep_v = n > pied, v > vol + 0.0005
        proche_n = pied > 0 and n >= SEUIL_PROCHE * pied
        proche_v = vol > 0 and v >= SEUIL_PROCHE * vol
        if dep_n or dep_v:
            niveau = "rouge"
        elif proche_n or proche_v:
            niveau = "orange"
        else:
            continue
        out.append({"titre": r["titre"], "essence": r["essence"], "pied": pied, "vol": vol, "n": n, "v": v,
                    "dep_n": dep_n, "dep_v": dep_v, "sans_permis": bool(r["sans_permis"]), "niveau": niveau,
                    "exces_n": max(n - pied, 0), "exces_v": max(v - vol, 0.0)})
    out.sort(key=lambda a: (a["niveau"] != "rouge", -a["exces_v"], -a["exces_n"]))
    return out


def _jauge(pct: float, rouge: bool) -> str:
    return (f'<div class="m4-jauge"><i style="width:{min(pct, 100):.0f}%;background:{"#B94A44" if rouge else "#52B788"}"></i></div>')


def carte_alerte(a: dict) -> str:
    rouge = a["niveau"] == "rouge"
    pct_n = a["n"] / a["pied"] * 100 if a["pied"] else (100 if a["n"] else 0)
    pct_v = a["v"] / a["vol"] * 100 if a["vol"] else (100 if a["v"] else 0)
    etiquette = "Sans permis" if a["sans_permis"] else ("Dépassement" if rouge else "Proche de la limite")
    exc_n = f' <span class="exc">+{a["exces_n"]}</span>' if a["dep_n"] else ""
    exc_v = f' <span class="exc">+{fr(a["exces_v"])} m³</span>' if a["dep_v"] else ""
    return (f'<div class="m4-al {a["niveau"]}"><div class="t"><b>{e(a["essence"].title())}</b> · Titre {e(a["titre"])}'
            f'<span class="m4-badge {"bad" if rouge else "warn"}">{etiquette}</span></div>'
            f'<div class="l"><span>Tiges</span><b class="{"r" if a["dep_n"] else ""}">{a["n"]} / {a["pied"]}</b>{exc_n}</div>{_jauge(pct_n, a["dep_n"])}'
            f'<div class="l"><span>Volume</span><b class="{"r" if a["dep_v"] else ""}">{fr(a["v"])} / {fr(a["vol"])} m³</b>{exc_v}</div>{_jauge(pct_v, a["dep_v"])}'
            f'</div>')


def vue_alertes(alertes):
    if alertes is None:
        st.markdown('<div class="m4-vide">Le permis n’est pas encore en ligne : ajoutez « permis » (et « reference_titres ») '
                    'aux tables de la synchronisation, puis relancez-la.</div>', unsafe_allow_html=True)
        return
    rouges = [a for a in alertes if a["niveau"] == "rouge"]
    st.markdown('<div class="m4-kpis three">'
                + kpi("Dépassements", f"{len(rouges)}", unite="", couleur="#B94A44", sous="titre × essence")
                + kpi("Tiges en trop", f"{sum(a['exces_n'] for a in rouges)}", unite="", couleur="#B94A44")
                + kpi("Volume en trop", fr(sum(a["exces_v"] for a in rouges)), couleur="#B94A44")
                + '</div>', unsafe_allow_html=True)
    if not alertes:
        st.markdown('<div class="m4-vide">Aucun dépassement du permis, et aucune essence proche de sa limite.</div>',
                    unsafe_allow_html=True)
        return
    st.caption("Abattu = cumul depuis le début, comparé au permis par titre et par essence (tiges et volume). "
               f"Orange : à partir de {int(SEUIL_PROCHE * 100)} % du permis.")
    st.markdown("".join(carte_alerte(a) for a in alertes), unsafe_allow_html=True)
    export = pd.DataFrame([{"Titre": a["titre"], "Essence": a["essence"].title(), "Tiges abattues": a["n"],
                            "Tiges autorisées": a["pied"], "Tiges en trop": a["exces_n"], "Volume abattu (m³)": round(a["v"], 3),
                            "Volume autorisé (m³)": round(a["vol"], 3), "Volume en trop (m³)": round(a["exces_v"], 3),
                            "Niveau": "Dépassement" if a["niveau"] == "rouge" else "Proche de la limite",
                            "Sans permis": "oui" if a["sans_permis"] else ""} for a in alertes])
    telecharger(export, "alertes_permis.csv", "dl_alertes")

@st.dialog("Alertes du permis", width="large")
def dialogue_alertes():
    titres, essences = filtres_globaux()
    try:
        alertes = charger_alertes(titres, essences)
    except Exception:
        alertes = None
    vue_alertes(alertes)


ICONES_EVT = {"connexion": "✅ Connexion", "echec": "❌ Échec", "blocage": "🔒 Blocage", "deconnexion": "↩ Déconnexion", "hors_ligne": "📥 Export hors connexion", "chargement": "🚚 Bordereau", "rapport": "📄 Rapport"}


def vue_journal():
    """Journal des connexions (réservé aux comptes listés dans les Secrets : [admin] ids = [...])."""
    try:
        lignes = requete("SELECT quand, identifiant, evenement, detail, appareil, ip FROM public.mobile_journal "
                         "ORDER BY quand DESC LIMIT 500")
    except Exception:
        st.markdown('<div class="m4-vide">Journal indisponible : lancez une fois « gerer_utilisateurs_mobile.py preparer » '
                    'sur le PC pour créer les tables.</div>', unsafe_allow_html=True)
        return
    if not lignes:
        st.markdown('<div class="m4-vide">Aucune connexion enregistrée pour le moment.</div>', unsafe_allow_html=True)
        return
    df = pd.DataFrame(lignes)
    df["quand"] = pd.to_datetime(df["quand"], utc=True).dt.tz_convert("Africa/Douala")
    sept = pd.Timestamp.now(tz="Africa/Douala") - pd.Timedelta(days=7)
    rec = df[df["quand"] >= sept]
    st.markdown('<div class="m4-kpis">'
                + kpi("Connexions (7 j)", f"{int((rec['evenement'] == 'connexion').sum())}", unite="", couleur="#2D6A4F",
                      sous=f"{rec.loc[rec['evenement'] == 'connexion', 'identifiant'].nunique()} compte(s)")
                + kpi("Échecs (7 j)", f"{int(rec['evenement'].isin(['echec', 'blocage']).sum())}", unite="", couleur="#B94A44")
                + '</div>', unsafe_allow_html=True)
    f = seg("Afficher", ["Tout", "Connexions", "Échecs"], default="Tout", key="jr_filtre",
                             label_visibility="collapsed") or "Tout"
    if f == "Connexions":
        df = df[df["evenement"] == "connexion"]
    elif f == "Échecs":
        df = df[df["evenement"].isin(["echec", "blocage"])]
    compte = st.text_input("Compte", key="jr_compte", label_visibility="collapsed", placeholder="Filtrer par compte…")
    if compte.strip():
        df = df[df["identifiant"].str.contains(compte.strip(), case=False, regex=False)]
    aff = pd.DataFrame({
        "Date": df["quand"].dt.strftime("%d/%m/%Y %H:%M"), "Compte": df["identifiant"],
        "Événement": df["evenement"].map(lambda x: ICONES_EVT.get(x, x)), "Détail": df["detail"].fillna(""),
        "Appareil": df["appareil"].fillna(""), "IP": df["ip"].fillna("")})
    st.dataframe(aff, hide_index=True, width="stretch", height=min(520, 38 + 35 * max(len(aff), 1)),
                 column_config={"Date": st.column_config.TextColumn(pinned=True)})
    st.caption("Heures de Douala · les 500 dernières lignes · visible uniquement par les comptes administrateurs.")


@st.dialog("Administration", width="large")
def dialogue_journal():
    n = len(demandes_en_attente())
    vue = seg("Vue", ["Connexions", "Demandes"], default="Demandes" if n else "Connexions", key="adm_vue",
              label_visibility="collapsed")
    if vue == "Demandes":
        st.markdown(f'<div class="m4-sec" style="margin-top:.2rem">Demandes de mot de passe ({n} en attente)</div>',
                    unsafe_allow_html=True)
        vue_demandes()
    else:
        vue_journal()
        try:
            n_jet = requete("SELECT count(*) AS n FROM public.mobile_jetons WHERE expire_le > now()")[0]["n"]
        except Exception:
            n_jet = None
        if n_jet is not None:
            st.markdown(f'<div class="m4-sec">Appareils mémorisés ({n_jet})</div>', unsafe_allow_html=True)
            if st.button("Déconnecter tous les appareils", width="stretch", key="adm_jetons", disabled=not n_jet,
                         help="Supprime la mémoire « Rester connecté » : chacun devra ressaisir son mot de passe."):
                if ecrire("DELETE FROM public.mobile_jetons"):
                    st.toast("Tous les appareils ont été déconnectés.")
                    st.rerun()


ORDRE_DF10 = ("ARRAY(SELECT CASE WHEN s ~ '^[0-9]+$' THEN lpad(s, 9, '0') ELSE s END "
              "FROM unnest(string_to_array(TRIM(df10), '/')) AS s)")
PAS_CARNET, PAS_RECAP = 30, 10          # lignes (Carnet) et DF10 (Recap) ajoutés à chaque « Afficher plus »


@st.cache_data(ttl=TTL_DONNEES, show_spinner=False)
def codes_minfof() -> dict:
    """Essence -> CODE MINFOF, lu dans la table Inventaire (dictionnaire vide si la table n'existe pas encore)."""
    try:
        lignes = requete("SELECT UPPER(TRIM(essence)) AS e, MIN(NULLIF(TRIM(code_minfof), '')) AS c FROM inventaire "
                         "WHERE TRIM(COALESCE(essence,'')) <> '' GROUP BY 1")
    except Exception:
        return {}
    return {r["e"]: r["c"] for r in lignes if r["c"]}


@st.cache_data(ttl=TTL_DONNEES, show_spinner=False)
def prix_fob() -> dict:
    """Essence (MAJUSCULES) -> valeur FOB par m³ (FCFA), lue dans la table Fob ; vide si elle n'existe pas encore."""
    try:
        lignes = requete("SELECT UPPER(TRIM(essence)) AS e, valeur_fob AS v FROM fob WHERE TRIM(COALESCE(essence,'')) <> ''")
    except (psycopg2.errors.UndefinedTable, psycopg2.errors.InsufficientPrivilege):
        return {}
    return {r["e"]: float(r["v"]) for r in lignes if r["v"] is not None}


def fcfa(v) -> str:
    """Montant en FCFA, arrondi à l'entier, espace fine insécable entre les milliers."""
    return f"{round(float(v or 0)):,}".replace(",", "\u202f")


def _clause_abattage(titre: list, essence: list, cherche: str, df10_seul: bool = False) -> tuple[str, list]:
    """Filtres communs aux deux vues. Le champ « DF10 » cherche un numéro de DF10 (début du numéro) ;
    la vue Carnet accepte aussi un code barre de grume."""
    w, p = ["TRIM(COALESCE(df10,'')) <> ''"], []
    if titre:
        w.append("TRIM(titre) = ANY(%s)")
        p.append(list(titre))
    if essence:
        w.append("UPPER(TRIM(essence)) = ANY(%s)")
        p.append(list(essence))
    if cherche:
        if df10_seul:
            w.append("df10 ILIKE %s")
            p.append(f"{cherche}%")
        else:
            w.append("(df10 ILIKE %s OR code_barre_abattage ILIKE %s)")
            p += [f"{cherche}%", f"%{cherche}%"]
    return " AND ".join(w), p


def _date_fr(d) -> str:
    return d.strftime("%d/%m/%Y") if d else ""


def _periode_fr(d1, d2) -> str:
    """Date d'un DF10 : « 03/11/2026 » ; si les grumes n'ont pas toutes la même date : « 03/11 → 05/11/2026 »."""
    if not d1:
        return "—"
    if d1 == d2 or not d2:
        return _date_fr(d1)
    return f"{d1:%d/%m} → {_date_fr(d2)}"


PIED_RAPPORT_DF10 = "SIGIF 2 - STBK - BATOURI"        # pied de page des rapports de DF10 (comme le classeur modèle)


def _mention_generation() -> str:
    """Mention discrète en bas de page des rapports."""
    return f"Généré par Mich4Track · {datetime.now(FUSEAU):%d/%m/%Y}"


def _periode_txt(d1, d2) -> str:
    """« 15/09/2026 » ou « du 15/09/2026 au 17/09/2026 » ; vide si aucune date."""
    if not d1:
        return ""
    if not d2 or d1 == d2:
        return d1.strftime("%d/%m/%Y")
    return f"du {d1:%d/%m/%Y} au {d2:%d/%m/%Y}"


def _donnees_df10(carnet: str) -> dict:
    """Grumes (abattage) et billes (billonnage) d'un DF10, titre forestier, dates et valeur FOB par essence."""
    cond = "split_part(TRIM(df10), '/', 1) = %s"
    grumes = requete("SELECT df10, code_barre_abattage AS cb, UPPER(TRIM(COALESCE(essence,''))) AS essence, dgb, dpb, longueur, volume, "
                     "TRIM(COALESCE(titre,'')) AS titre, date "
                     f"FROM abattage WHERE {cond} ORDER BY {ORDRE_DF10}, code_barre_abattage", (carnet,))
    billes = requete("SELECT code_barre, sequence, df10, UPPER(TRIM(COALESCE(essence,''))) AS essence, dgb, dpb, longueur, volume, "
                     "UPPER(TRIM(COALESCE(statut,''))) AS statut, TRIM(COALESCE(titre,'')) AS titre, date_billonnage AS date "
                     f"FROM billonnage WHERE {cond} ORDER BY {ORDRE_DF10}, code_barre", (carnet,))
    titres = [r["titre"] for r in grumes + billes if r["titre"]]
    titre = max(set(titres), key=titres.count) if titres else ""
    dates = lambda lst: [r["date"] for r in lst if r["date"]]
    da, db = dates(grumes), dates(billes)
    return {"carnet": carnet, "titre": titre, "grumes": grumes, "billes": billes, "fob": prix_fob(),
            "date_abat": _periode_txt(min(da) if da else None, max(da) if da else None),
            "date_prep": _periode_txt(min(db) if db else None, max(db) if db else None)}


def rapport_df10_pdf(carnet: str, parc: bool = False) -> bytes:
    """Rapport PDF d'un DF10 : même contenu que le Word (en-tête avec logo, titre forestier, N° du DF10 et date ; tableaux ABATTAGE
    puis PRÉPARATION ; pied « SIGIF 2 - STBK - BATOURI » avec pagination), mise en page fixe pour l'impression en noir et blanc."""
    from io import BytesIO
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.units import cm
    from reportlab.lib.utils import ImageReader
    from reportlab.pdfgen import canvas as cv
    from reportlab.platypus import BaseDocTemplate, Frame, NextPageTemplate, PageBreak, PageTemplate, Paragraph, Spacer, Table, TableStyle
    from reportlab.lib.styles import ParagraphStyle
    d = _donnees_df10(carnet)
    grumes, billes, fob = d["grumes"], d["billes"], d["fob"]
    if parc:                                                        # version parc : préparation seule, billes abandonnées exclues
        billes = [b for b in billes if b["statut"] != "ABANDON"]
    logo = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logo_societe.png")
    W, H = A4
    MG = 1.5 * cm
    NOIR, G_ENTETE, G_ZEBRE, G_ABANDON, G_FIN = colors.black, colors.HexColor("#D9D9D9"), colors.HexColor("#F2F2F2"), colors.HexColor("#BFBFBF"), colors.HexColor("#595959")
    mention = _mention_generation()

    class Num(cv.Canvas):
        """Canevas qui connaît le nombre total de pages pour écrire « page x / y » dans le pied de page."""
        def __init__(self, *a, **k):
            super().__init__(*a, **k)
            self._etats = []

        def showPage(self):
            self._etats.append(dict(self.__dict__))
            self._startPage()

        def save(self):
            total = len(self._etats)
            for e in self._etats:
                self.__dict__.update(e)
                self.setStrokeColor(NOIR); self.setLineWidth(0.6)
                self.line(MG, 1.55 * cm, W - MG, 1.55 * cm)
                self.setFillColor(NOIR); self.setFont("Times-Roman", 10)
                self.drawCentredString(W / 2, 1.08 * cm, f"{PIED_RAPPORT_DF10}   ·   page {self._pageNumber} / {total}")
                self.setFillColor(colors.HexColor("#808080")); self.setFont("Times-Roman", 6.5)
                self.drawCentredString(W / 2, 0.62 * cm, mention)
                super().showPage()
            super().save()

    def entete(c, doc, ligne2, dt):
        if os.path.exists(logo):
            c.drawImage(ImageReader(logo), MG + 0.2 * cm, H - 1.0 * cm - 2.1 * cm, width=2.1 * cm, height=2.1 * cm, mask="auto", preserveAspectRatio=True)
        c.setFillColor(NOIR)
        y = H - 1.55 * cm
        for txt, police, taille in ((d["titre"], "Times-Bold", 13), (ligne2, "Times-Bold", 16), (dt, "Times-Roman", 11)):
            if txt:
                c.setFont(police, taille)
                c.drawCentredString(W / 2, y - taille * 0.7, txt)
                y -= taille * 1.25
        c.setStrokeColor(NOIR); c.setLineWidth(1)
        c.line(MG, H - 3.3 * cm, W - MG, H - 3.3 * cm)

    def decimales(valeurs, maxi):
        n_ = 0
        for v in valeurs:
            if v is not None:
                txt = f"{float(v):.{maxi}f}".rstrip("0")
                n_ = max(n_, len(txt.split(".")[1]) if "." in txt else 0)
        return n_

    def fmt(v, dec):
        return "" if v is None else f"{float(v):.{dec}f}".replace(".", ",")

    def tableau(entetes, lignes, largeurs_cm, alignements, total=None, zebre=False, abandon=None, groupes=None):
        data = [entetes] + lignes
        n = len(lignes)
        if total:
            data.append(["TOTAL"] + [""] * total[0] + [total[1]] + [""] * (len(entetes) - total[0] - 2))
        t = Table(data, colWidths=[w * cm for w in largeurs_cm], repeatRows=1, splitByRow=1)
        nc = len(entetes)
        st = [("FONTNAME", (0, 0), (-1, -1), "Times-Roman"), ("FONTSIZE", (0, 0), (-1, -1), 11), ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
              ("TOPPADDING", (0, 0), (-1, -1), 4.5), ("BOTTOMPADDING", (0, 0), (-1, -1), 4.5), ("LEFTPADDING", (0, 0), (-1, -1), 4),
              ("RIGHTPADDING", (0, 0), (-1, -1), 4), ("TEXTCOLOR", (0, 0), (-1, -1), NOIR),
              ("INNERGRID", (0, 0), (-1, -1), 0.5, G_FIN), ("BOX", (0, 0), (-1, -1), 1.5, NOIR),
              ("BACKGROUND", (0, 0), (-1, 0), G_ENTETE), ("FONTNAME", (0, 0), (-1, 0), "Times-Bold"), ("ALIGN", (0, 0), (-1, 0), "CENTER"),
              ("LINEBELOW", (0, 0), (-1, 0), 1.5, NOIR)]
        for j, a in enumerate(alignements):
            if n:
                st.append(("ALIGN", (j, 1), (j, n), a))
            if a == "RIGHT":
                st.append(("RIGHTPADDING", (j, 0), (j, -1), 8))
        if n:
            st.append(("FONTNAME", (0, 1), (0, n), "Times-Bold"))                      # N° de DF10 en gras : repère de lecture
        if zebre and n:
            st.append(("ROWBACKGROUNDS", (0, 1), (-1, n), [colors.white, G_ZEBRE]))
        for i in range(n):
            if abandon and abandon[i]:
                st += [("BACKGROUND", (0, i + 1), (-1, i + 1), G_ABANDON), ("FONTNAME", (-1, i + 1), (-1, i + 1), "Times-Bold")]
            if groupes and i > 0 and groupes[i] != groupes[i - 1]:
                st.append(("LINEABOVE", (0, i + 1), (-1, i + 1), 0.9, NOIR))            # une grume = un groupe de billes
        if total:
            r = n + 1
            st += [("SPAN", (0, r), (total[0], r)), ("BACKGROUND", (0, r), (-1, r), G_ENTETE), ("FONTNAME", (0, r), (-1, r), "Times-Bold"),
                   ("FONTSIZE", (0, r), (-1, r), 12), ("ALIGN", (0, r), (total[0], r), "CENTER"), ("ALIGN", (total[0] + 1, r), (total[0] + 1, r), "RIGHT"),
                   ("LINEABOVE", (0, r), (-1, r), 1.5, NOIR), ("TOPPADDING", (0, r), (-1, r), 6), ("BOTTOMPADDING", (0, r), (-1, r), 6)]
        t.setStyle(TableStyle(st))
        return t

    util = (W - 2 * MG) / cm
    story = []
    # ---- ABATTAGE
    avec_fob = bool(fob)
    if parc:
        grumes = []
    ent = ["DF10", "CB GRUME", "ESSENCE", "DGB", "DPB", "Dm", "LONG.", "VOLUME"] + (["V. FOB"] if avec_fob else [])
    dm_ = [((float(g["dgb"]) + float(g["dpb"])) / 2) if g["dgb"] is not None and g["dpb"] is not None else None for g in grumes]
    dg, dp = decimales([g["dgb"] for g in grumes], 1), decimales([g["dpb"] for g in grumes], 1)
    dm, dl = decimales(dm_, 1), decimales([g["longueur"] for g in grumes], 2)
    lig = []
    for g, m in zip(grumes, dm_):
        lig.append([g["df10"], g["cb"] or "", g["essence"], fmt(g["dgb"], dg), fmt(g["dpb"], dp), fmt(m, dm), fmt(g["longueur"], dl), fmt(g["volume"], 3)]
                   + ([f"{round(fob[g['essence']]):,}".replace(",", " ") if g["essence"] in fob else ""] if avec_fob else []))
    larg = [2.4, 2.8, 2.6, 1.4, 1.4, 1.5, 1.7, 2.1, 2.1] if avec_fob else [3.0, 3.6, 3.2, 1.7, 1.7, 1.9, 2.0, 0.9]
    if not avec_fob:
        larg[-1] = util - sum(larg[:-1])
    ali = ["CENTER"] * 3 + ["RIGHT"] * (len(ent) - 3)
    if parc:
        pass
    elif lig:
        story.append(tableau(ent, lig, larg, ali, total=(6, fmt(sum(float(g["volume"] or 0) for g in grumes), 3)), zebre=True))
    else:
        story.append(Paragraph("Aucune grume enregistrée pour ce DF10.", ParagraphStyle("v", fontName="Times-Roman", fontSize=11)))
    # ---- PRÉPARATION
    if not parc:
        story += [NextPageTemplate("prep"), PageBreak()]
    db = (decimales([b["dgb"] for b in billes], 1), decimales([b["dpb"] for b in billes], 1), decimales([b["longueur"] for b in billes], 2))
    lig2, ab, grp = [], [], []
    for b in billes:
        lig2.append([b["code_barre"] or "", b["sequence"] or "", b["df10"], b["essence"], fmt(b["dgb"], db[0]), fmt(b["dpb"], db[1]),
                     fmt(b["longueur"], db[2]), fmt(b["volume"], 3), "AB" if b["statut"] == "ABANDON" else ""])
        ab.append(b["statut"] == "ABANDON")
        grp.append((b["df10"] or "").rsplit("/", 1)[0])
    if lig2:
        if parc:
            story.append(tableau(["CB BILLON", "SEQUENCE", "DF10", "ESSENCE", "DGB", "DPB", "LONG", "VOL."], [l[:8] for l in lig2],
                                 [2.6, 3.4, 2.6, 2.8, 1.5, 1.5, 1.6, 1.9], ["CENTER"] * 4 + ["RIGHT"] * 4, groupes=grp))
        else:
            story.append(tableau(["CB BILLON", "SEQUENCE", "DF10", "ESSENCE", "DGB", "DPB", "LONG", "VOL.", ""], lig2,
                                 [2.5, 3.2, 2.5, 2.6, 1.4, 1.4, 1.5, 1.9, 1.0], ["CENTER"] * 4 + ["RIGHT"] * 4 + ["CENTER"], abandon=ab, groupes=grp))
        if any(ab) and not parc:
            story += [Spacer(1, 8), Paragraph("AB : bille en statut Abandon", ParagraphStyle("l", fontName="Times-Italic", fontSize=10))]
    else:
        story.append(Paragraph("Aucune bille enregistrée pour ce DF10.", ParagraphStyle("v", fontName="Times-Roman", fontSize=11)))
    sortie = BytesIO()
    doc = BaseDocTemplate(sortie, pagesize=A4, leftMargin=MG, rightMargin=MG, topMargin=3.6 * cm, bottomMargin=2.0 * cm,
                          title=f"DF10 {carnet}", author="Mich4Track")
    cadre = Frame(MG, 2.0 * cm, W - 2 * MG, H - 3.6 * cm - 2.0 * cm, leftPadding=0, rightPadding=0, topPadding=0, bottomPadding=0)
    if parc:
        doc.addPageTemplates([PageTemplate(id="prep", frames=[cadre], onPage=lambda c, dc: entete(c, dc, f"PREPARATION N° {carnet}", d["date_prep"]))])
        doc.build(story, canvasmaker=Num)
        return sortie.getvalue()
    doc.addPageTemplates([PageTemplate(id="abat", frames=[cadre], onPage=lambda c, dc: entete(c, dc, f"DF10 N° {carnet}", d["date_abat"])),
                          PageTemplate(id="prep", frames=[cadre], onPage=lambda c, dc: entete(c, dc, f"PREPARATION N° {carnet}", d["date_prep"]))])
    doc.build(story, canvasmaker=Num)
    return sortie.getvalue()


def bloc_rapport_df10(titre: list, essence: list, cherche: str):
    """Téléchargement du rapport PDF d'un DF10 (nom du fichier = n° du DF10)."""
    import functools
    clause, p = _clause_abattage(titre, essence, cherche, df10_seul=True)
    carnets = _recap_carnets(clause, p)
    with st.expander("Rapport d'un DF10 (PDF)", icon=":material/description:"):
        if not carnets:
            st.caption("Aucun DF10 pour ces critères.")
            return
        par_num = {c["carnet"]: c for c in carnets[:300]}
        choix = st.selectbox("DF10", list(par_num), key="ab_rap_df10", label_visibility="collapsed",
                             format_func=lambda k: f"{k} · {fr(par_num[k]['n'], 0)} grumes · {fr(par_num[k]['v'])} m³ · "
                                                   f"{_periode_fr(par_num[k]['d1'], par_num[k]['d2'])}")
        nom = re.sub(r"[^\w.-]", "_", choix)
        st.download_button(f"Télécharger le rapport du DF10 {choix} (PDF)", functools.partial(rapport_df10_pdf, choix),
                           file_name=nom + ".pdf", width="stretch", key="ab_rap_dl_p", type="primary", icon=":material/download:",
                           mime="application/pdf")
        st.caption("Prêt à imprimer (noir et blanc) : logo, titre forestier et date en en-tête ; ABATTAGE puis PRÉPARATION ; pied « SIGIF 2 - STBK - BATOURI ».")
        st.download_button(f"Version parc du DF10 {choix} (PDF)", functools.partial(rapport_df10_pdf, choix, True),
                           file_name=nom + "_parc.pdf", width="stretch", key="ab_rap_dl_parc", icon=":material/forest:",
                           mime="application/pdf")
        st.caption("Pour le parc : PRÉPARATION seule, sans les billes abandonnées et sans l'abattage.")
        if len(carnets) > 300:
            st.caption("Les 300 DF10 les plus récents sont proposés : précisez le numéro dans le champ DF10.")


def vue_abattage(titre: list, essence: list):
    """Abattage : deux vues, Carnet (liste des grumes) et Recap (récapitulatif par DF10), sous un filtre DF10 commun."""
    st.markdown('<div class="m4-sec">DF10</div>', unsafe_allow_html=True)
    cherche = st.text_input("DF10", key="ab_q", placeholder="N° de DF10, ex. 54756",
                            label_visibility="collapsed").strip()
    vue = seg("Vue", ["Carnet", "Recap"], key="ab_vue", default="Carnet", label_visibility="collapsed")
    signature = (tuple(titre), tuple(essence), cherche, vue)
    if st.session_state.get("ab_sig") != signature:     # filtre ou vue modifié : on repart des premières lignes
        st.session_state["ab_sig"] = signature
        st.session_state["ab_nb"], st.session_state["rc_nb"] = PAS_CARNET, PAS_RECAP
    actifs = [("Titre : " + ", ".join(titre)) if titre else "", ("Essence : " + ", ".join(essence)) if essence else ""]
    if any(actifs):
        st.caption("Filtres du haut appliqués — " + " · ".join(a for a in actifs if a))
    if vue == "Carnet":
        _abattage_carnet(titre, essence, cherche)
    else:
        _abattage_recap(titre, essence, cherche)
    bloc_rapport_df10(titre, essence, cherche)


def _abattage_carnet(titre: list, essence: list, cherche: str):
    """Liste des grumes abattues : DF10, CB grume, essence, CODE MINFOF, DGB, DPB, DM, longueur, volume."""
    clause, p = _clause_abattage(titre, essence, cherche)
    tot = q(f"SELECT COUNT(*) AS n, COALESCE(SUM(volume),0) AS v FROM abattage WHERE {clause}", p)[0]
    c1, c2 = st.columns(2)
    c1.markdown(kpi("Grumes", fr(tot["n"], 0), "", "#2D6A4F"), unsafe_allow_html=True)
    c2.markdown(kpi("Volume", fr(tot["v"]), "m³", "#B5651D"), unsafe_allow_html=True)
    if not tot["n"]:
        st.markdown('<div class="m4-vide">Aucune grume abattue pour ces critères.</div>', unsafe_allow_html=True)
        return
    fob = prix_fob()
    nb = st.session_state.get("ab_nb", PAS_CARNET)
    colonnes = "df10, code_barre_abattage AS cb, UPPER(TRIM(essence)) AS essence, dgb, dpb, longueur, volume"
    ordre = f"ORDER BY {ORDRE_DF10}, code_barre_abattage"
    lignes = q(f"SELECT {colonnes} FROM abattage WHERE {clause} {ordre} LIMIT %s", p + [nb])
    codes = codes_minfof()

    def dm(r):
        try:
            return fr((float(r["dgb"] or 0) + float(r["dpb"] or 0)) / 2, 1)
        except (TypeError, ValueError):
            return "—"

    def val_fob(r) -> float | None:
        """Valeur FOB de l'essence de la grume (prix tel que saisi dans la table Fob, sans calcul)."""
        return fob.get(r["essence"] or "")

    corps = [[f"<b>{e(r['df10'])}</b>", e(r["cb"] or "—"), e(r["essence"] or "—"), e(codes.get(r["essence"]) or "—"),
              fr(r["dgb"], 0), fr(r["dpb"], 0), dm(r), fr(r["longueur"], 2), fr(r["volume"])]
             + ([("—" if val_fob(r) is None else fcfa(val_fob(r)))] if fob else []) for r in lignes]
    st.markdown('<style>.m4-ab th,.m4-ab td{padding:.4rem .16rem !important;font-size:.6rem !important;letter-spacing:0 !important}'
                '.m4-ab th{font-size:.52rem !important}.m4-ab th,.m4-ab td{text-align:right !important}'
                '.m4-ab th:nth-child(-n+3),.m4-ab td:nth-child(-n+3){text-align:left !important}'
                '.m4-ab th:nth-child(4),.m4-ab td:nth-child(4){text-align:center !important}'
                '.m4-ab th:last-child,.m4-ab td:last-child{padding-right:.5rem !important}'
                '.m4-ab td:first-child,.m4-ab th:first-child{padding-left:.4rem !important}</style>'
                + _table_html(["DF10", "CB grume", "Essence", "Code", "DGB", "DPB", "DM", "Long.", "Volume"] + (["Valeur FOB"] if fob else []),
                            corps, "m4-ab"),
                unsafe_allow_html=True)
    st.caption(f"{len(lignes)} grume(s) affichée(s) sur {fr(tot['n'], 0)} · Code = code MINFOF de l'essence · "
               "DM = (DGB + DPB) / 2 · diamètres en cm, longueur en m"
               + (" · Valeur FOB = valeur de l'essence (FCFA)" if fob else ""))
    if len(lignes) < tot["n"]:
        if st.button(f"Afficher {PAS_CARNET} de plus", width="stretch", key="ab_plus"):
            st.session_state["ab_nb"] = nb + PAS_CARNET
            st.rerun()
    toutes = q(f"SELECT {colonnes} FROM abattage WHERE {clause} {ordre}", p)
    csv = "DF10;CB GRUME;ESSENCE;CODE;DGB;DPB;DM;LONG.;VOLUME" + (";VALEUR FOB" if fob else "") + "\n" + "\n".join(
        ";".join([str(r["df10"]), str(r["cb"] or ""), str(r["essence"] or ""), str(codes.get(r["essence"]) or ""),
                  str(r["dgb"] or ""), str(r["dpb"] or ""), dm(r), fr(r["longueur"], 2), fr(r["volume"])]
                 + ([("" if val_fob(r) is None else str(round(val_fob(r))))] if fob else [])) for r in toutes)
    st.download_button(f"Exporter en CSV ({fr(len(toutes), 0)} grumes)", ("﻿" + csv).encode("utf-8"),
                       file_name="abattage_carnet.csv", mime="text/csv", width="stretch", key="ab_csv", type="primary")


def _recap_carnets(clause: str, p: list) -> list[dict]:
    """Un dict par DF10 (n° de carnet) : date(s), essences abattues (grumes, volume), totaux. Plus récent d'abord."""
    lignes = q("SELECT split_part(TRIM(df10), '/', 1) AS carnet, UPPER(TRIM(COALESCE(essence,''))) AS essence, "
               "COUNT(*) AS n, COALESCE(SUM(volume),0) AS v, MIN(date) AS d1, MAX(date) AS d2 "
               f"FROM abattage WHERE {clause} GROUP BY 1, 2", p)
    carnets: dict[str, dict] = {}
    for r in lignes:
        c = carnets.setdefault(r["carnet"], {"carnet": r["carnet"], "d1": None, "d2": None, "ess": [], "n": 0, "v": 0.0})
        c["ess"].append((r["essence"] or "SANS ESSENCE", int(r["n"]), float(r["v"])))
        c["n"] += int(r["n"])
        c["v"] += float(r["v"])
        if r["d1"] and (c["d1"] is None or r["d1"] < c["d1"]):
            c["d1"] = r["d1"]
        if r["d2"] and (c["d2"] is None or r["d2"] > c["d2"]):
            c["d2"] = r["d2"]
    liste = list(carnets.values())
    for c in liste:
        c["ess"].sort(key=lambda x: (-x[2], x[0]))               # volume décroissant
    liste.sort(key=lambda c: (c["d2"] or date.min, cle_naturelle(c["carnet"])), reverse=True)
    return liste


def recap_xlsx(carnets: list[dict], titre: list, essence: list, cherche: str) -> bytes:
    """Récapitulatif par DF10 en Excel, mis en page comme à l'écran : numéro et date du DF10 en cellule fusionnée
    (texte vertical), une ligne par essence abattue, ligne Total grisée, total général en pied."""
    from io import BytesIO
    from openpyxl import Workbook
    from openpyxl.styles import Alignment, Border, Font, PatternFill, Side
    try:
        from openpyxl.cell.rich_text import CellRichText, TextBlock
        from openpyxl.cell.text import InlineFont
    except ImportError:
        CellRichText = None
    vert, vert_clair, gris = "2D6A4F", "E3EFE5", "D9D9D9"
    fin = Side(style="thin", color="8A9A8E")
    moyen = Side(style="medium", color="2D6A4F")
    cadre = Border(left=fin, right=fin, top=fin, bottom=fin)
    wb = Workbook()
    ws = wb.active
    ws.title = "Recap DF10"
    ws.sheet_view.showGridLines = False
    for col, larg in zip("ABCD", (15, 24, 12, 17)):
        ws.column_dimensions[col].width = larg
    ws["A1"] = "Récapitulatif de l'abattage par DF10"
    ws["A1"].font = Font(name="Calibri", size=15, bold=True, color=vert)
    filtres = [("Titre : " + ", ".join(titre)) if titre else "Tous les titres",
               ("Essence : " + ", ".join(essence)) if essence else "Toutes les essences"]
    if cherche:
        filtres.append(f"DF10 : {cherche}…")
    ws["A2"] = " · ".join(filtres) + f" · édité le {datetime.now(FUSEAU):%d/%m/%Y à %H:%M}"
    ws["A2"].font = Font(name="Calibri", size=9, italic=True, color="5A6F60")
    ligne = 4
    for col, texte in zip("ABCD", ("DF10", "ESSENCE", "GRUMES", "VOLUME (m³)")):
        c = ws[f"{col}{ligne}"]
        c.value = texte
        c.font = Font(name="Calibri", size=10, bold=True, color="FFFFFF")
        c.fill = PatternFill("solid", fgColor=vert)
        c.alignment = Alignment(horizontal="center", vertical="center")
        c.border = cadre
    ws.row_dimensions[ligne].height = 22
    ws.freeze_panes = "A5"
    ligne += 1
    for c in carnets:
        debut, nb = ligne, len(c["ess"]) + 1
        hauteur = max(22.0, 74.0 / nb)                       # assez haut pour le texte vertical d'un bloc court
        for n_ess, n, v in c["ess"]:
            ws[f"B{ligne}"], ws[f"C{ligne}"], ws[f"D{ligne}"] = n_ess, n, v
            ws[f"C{ligne}"].number_format, ws[f"D{ligne}"].number_format = "#,##0", "#,##0.000"
            ws.row_dimensions[ligne].height = hauteur
            ligne += 1
        ws[f"B{ligne}"], ws[f"C{ligne}"], ws[f"D{ligne}"] = "Total", c["n"], c["v"]
        ws[f"C{ligne}"].number_format, ws[f"D{ligne}"].number_format = "#,##0", "#,##0.000"
        ws.row_dimensions[ligne].height = hauteur
        for r in range(debut, ligne + 1):
            for col in "ABCD":
                cell = ws[f"{col}{r}"]
                cell.border = Border(left=fin, right=fin, bottom=fin, top=moyen if r == debut else fin)
                if col == "B":
                    cell.alignment = Alignment(horizontal="left", vertical="center", indent=1)
                elif col in "CD":
                    cell.alignment = Alignment(horizontal="center" if col == "C" else "right", vertical="center",
                                               indent=0 if col == "C" else 1)
                cell.font = Font(name="Calibri", size=10, bold=(r == ligne))
                if r == ligne:
                    cell.fill = PatternFill("solid", fgColor=gris)
        ws.merge_cells(f"A{debut}:A{ligne}")
        a = ws[f"A{debut}"]
        periode = _periode_fr(c["d1"], c["d2"])
        if CellRichText:
            a.value = CellRichText(TextBlock(InlineFont(rFont="Calibri", sz=13, b=True), c["carnet"] + "\n"),
                                   TextBlock(InlineFont(rFont="Calibri", sz=9, color="5A6F60"), periode))
        else:
            a.value = f"{c['carnet']}\n{periode}"
        a.alignment = Alignment(horizontal="center", vertical="center", text_rotation=90, wrap_text=True)
        a.fill = PatternFill("solid", fgColor=vert_clair)
        ligne += 1
    ws[f"A{ligne}"] = f"TOTAL GÉNÉRAL — {len(carnets)} DF10"
    ws[f"C{ligne}"], ws[f"D{ligne}"] = sum(c["n"] for c in carnets), sum(c["v"] for c in carnets)
    ws[f"C{ligne}"].number_format, ws[f"D{ligne}"].number_format = "#,##0", "#,##0.000"
    ws.merge_cells(f"A{ligne}:B{ligne}")
    for col in "ABCD":
        cell = ws[f"{col}{ligne}"]
        cell.font = Font(name="Calibri", size=11, bold=True, color="FFFFFF")
        cell.fill = PatternFill("solid", fgColor=vert)
        cell.border = cadre
        cell.alignment = Alignment(horizontal="left" if col == "A" else ("center" if col == "C" else "right"),
                                   vertical="center", indent=1 if col in "AD" else 0)
    ws.row_dimensions[ligne].height = 24
    ws.print_title_rows = "4:4"
    ws.page_setup.orientation, ws.page_setup.paperSize, ws.page_setup.fitToWidth, ws.page_setup.fitToHeight = "portrait", 9, 1, 0
    ws.sheet_properties.pageSetUpPr.fitToPage = True
    ws.print_options.horizontalCentered = True
    ws.oddFooter.center.text = "© Mich4Track — page &P / &N"
    sortie = BytesIO()
    wb.save(sortie)
    return sortie.getvalue()


def _abattage_recap(titre: list, essence: list, cherche: str):
    """Récapitulatif par DF10 : essences abattues, grumes, volume, total. 10 DF10 à la fois."""
    clause, p = _clause_abattage(titre, essence, cherche, df10_seul=True)
    carnets = _recap_carnets(clause, p)
    c1, c2 = st.columns(2)
    n_grumes = sum(c["n"] for c in carnets)
    c1.markdown(kpi("DF10", fr(len(carnets), 0), "", "#2D6A4F", sous=f"{fr(n_grumes, 0)} grume(s)"), unsafe_allow_html=True)
    v_total = sum(c["v"] for c in carnets)
    c2.markdown(kpi("Volume", fr(v_total), "m³", "#B5651D",
                    sous=f"{fr(v_total / n_grumes, 3)} m³ par grume" if n_grumes else ""), unsafe_allow_html=True)
    if not carnets:
        st.markdown('<div class="m4-vide">Aucun DF10 pour ces critères.</div>', unsafe_allow_html=True)
        return
    nb = st.session_state.get("rc_nb", PAS_RECAP)
    visibles = carnets[:nb]
    blocs = []
    for c in visibles:
        lignes = "".join(f'<tr><td class="e">{e(n_ess)}</td><td>{fr(n, 0)}</td><td>{fr(v)}</td></tr>'
                         for n_ess, n, v in c["ess"])
        blocs.append(
            f'<tbody><tr><td class="id" rowspan="{len(c["ess"]) + 1}"><div><b>{e(c["carnet"])}</b>'
            f'<small>{e(_periode_fr(c["d1"], c["d2"]))}</small></div></td>'
            f'<td class="e">{e(c["ess"][0][0])}</td><td>{fr(c["ess"][0][1], 0)}</td><td>{fr(c["ess"][0][2])}</td></tr>'
            + lignes.split("</tr>", 1)[1]
            + f'<tr class="t"><td class="e">Total</td><td>{fr(c["n"], 0)}</td><td>{fr(c["v"])}</td></tr></tbody>')
    st.markdown(
        '<style>.m4-rc-wrap{border:1px solid var(--border);border-radius:14px;background:var(--surface);overflow:hidden}'
        'table.m4-rc{border-collapse:collapse;width:100%;font-size:.74rem;font-variant-numeric:tabular-nums}'
        '.m4-rc thead th{background:var(--soft);color:var(--muted);font-weight:700;font-size:.6rem;text-transform:uppercase;'
        'letter-spacing:.05em;padding:.5rem .45rem;text-align:right;border-bottom:1px solid var(--border)}'
        '.m4-rc thead th:nth-child(-n+2){text-align:left}.m4-rc thead th:first-child{text-align:center}'
        '.m4-rc td{padding:.46rem .5rem;text-align:right;border-bottom:1px solid var(--border);color:var(--text)}'
        '.m4-rc td.e{text-align:left;font-weight:600;letter-spacing:.01em}'
        '.m4-rc td.id{width:2.7rem;padding:.3rem .1rem;text-align:center;background:var(--alt);'
        'border-right:1px solid var(--border)}'
        '.m4-rc td.id div{writing-mode:vertical-rl;transform:rotate(180deg);display:inline-flex;gap:.45rem;'
        'align-items:center;justify-content:center;white-space:nowrap;margin:0 auto}'
        '.m4-rc td.id b{font-size:.82rem;color:var(--text)}.m4-rc td.id small{font-size:.56rem;color:var(--muted)}'
        '.m4-rc tr.t td{background:var(--soft);font-weight:700}.m4-rc tr.t td.e{font-weight:800}'
        '.m4-rc tbody + tbody tr:first-child td{border-top:2px solid var(--border)}'
        '</style><div class="m4-rc-wrap"><table class="m4-rc"><thead><tr><th>DF10</th><th>Essence</th><th>Grumes</th>'
        '<th>Volume (m³)</th></tr></thead>' + "".join(blocs) + '</table></div>', unsafe_allow_html=True)
    st.caption(f"{len(visibles)} DF10 affiché(s) sur {fr(len(carnets), 0)} · du plus récent au plus ancien · "
               "volumes en m³, essences abattues uniquement")
    if len(visibles) < len(carnets):
        if st.button(f"Afficher {PAS_RECAP} de plus", width="stretch", key="rc_plus"):
            st.session_state["rc_nb"] = nb + PAS_RECAP
            st.rerun()
    st.download_button(f"Exporter en Excel ({fr(len(carnets), 0)} DF10)", recap_xlsx(carnets, titre, essence, cherche),
                       file_name="abattage_recap.xlsx", width="stretch", key="rc_xlsx", type="primary",
                       mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")


# Carte des arbres abattus : contour du titre (dossier contours/, fichiers GeoJSON) + positions, colorés par essence
DOSSIER_CONTOURS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "contours")


@st.cache_data(ttl=TTL_DONNEES, show_spinner=False)
def carte_html(titre_sel: str):
    """(page HTML, compteurs) de la carte d'un titre. Lecture seule : un SELECT sur abattage."""
    lignes = requete(carte_abattage.SQL_TIGES, (titre_sel,))
    tiges = carte_abattage.tiges_depuis_lignes([tuple(r.values()) for r in lignes])
    if not tiges:
        return None, None
    contours = carte_abattage.contours_pour_titre(DOSSIER_CONTOURS, titre_sel)
    if not hasattr(carte_abattage, "SQL_INVENTAIRE"):
        raise RuntimeError("carte_abattage.py est une ancienne version : remplacez-le par la dernière (à côté de mobile_app.py).")
    try:                                                 # inventaire facultatif (table absente = pas de « Vue générale »)
        inv = carte_abattage.inventaire_depuis_lignes(
            [tuple(r.values()) for r in requete(carte_abattage.SQL_INVENTAIRE, (titre_sel,))])
    except Exception:
        inv = []
    html_page, data = carte_abattage.html_carte(titre_sel, contours, tiges, inventaire=inv)
    data["contour"] = bool(contours)
    return html_page, data


def vue_carte(titre: list):
    """Carte d'un titre. Rien n'est chargé tant que l'on n'a pas touché « Afficher la carte »."""
    st.markdown('<div class="m4-sec">Carte</div>', unsafe_allow_html=True)
    try:
        titres, _ = listes_filtres()
    except Exception:
        titres = []
    if not titres:
        st.markdown('<div class="m4-vide">Aucun titre disponible.</div>', unsafe_allow_html=True)
        return
    defaut = titre[0] if len(titre) == 1 and titre[0] in titres else None
    choix = st.selectbox("Titre", titres, index=titres.index(defaut) if defaut else None,
                         placeholder="Choisir un titre", key="carte_titre", label_visibility="collapsed")
    if choix:
        st.session_state["carte_affiche"] = choix if st.button("Afficher la carte", width="stretch", key="carte_go", type="primary") \
            or st.session_state.get("carte_affiche") == choix else None
    affiche = st.session_state.get("carte_affiche")
    if not affiche:
        st.caption("Choisissez un titre puis touchez « Afficher la carte » : contour, arbres abattus par essence, "
                   "curseur de dates et export en image.")
        return
    html_page, data = carte_html(affiche)
    if not html_page:
        st.markdown('<div class="m4-vide">Aucun arbre abattu pour ce titre.</div>', unsafe_allow_html=True)
        return
    c1, c2 = st.columns(2)
    c1.markdown(kpi("Arbres placés", fr(len(data["points"]), 0), "", "#2D6A4F"), unsafe_allow_html=True)
    vol = sum(p[3] for p in data["points"])
    c2.markdown(kpi("Volume", fr(vol, 3), "m³", "#B5651D"), unsafe_allow_html=True)
    st.iframe(html_page, height=620)
    notes = []
    if not data["contour"]:
        notes.append("contour non fourni pour ce titre")
    if data["hors_contour"]:
        notes.append(f"{data['hors_contour']} arbre(s) hors contour")
    if data["sans_position"]:
        notes.append(f"{data['sans_position']} sans position")
    if notes:
        st.caption(" · ".join(notes))
    st.download_button("Télécharger la carte (HTML)", html_page.encode("utf-8"),
                       file_name="Carte_" + re.sub(r"[^A-Za-z0-9]+", "", affiche) + ".html", mime="text/html",
                       width="stretch", key="carte_dl")


# Affichage PC : mêmes pages, mise en page élargie à partir de 980 px de large (le téléphone reste inchangé)
CSS_PC = """<style>
@media (min-width:980px){
  .block-container{ max-width:1180px !important; padding:1.4rem 2.2rem 4rem !important; }
  .m4-kpis{ grid-template-columns:repeat(auto-fit,minmax(190px,1fr)); }
  .m4-kpis.three{ grid-template-columns:repeat(3,1fr); }
  [data-testid="stMarkdownContainer"]:has(> details.m4-card){ display:grid; grid-template-columns:repeat(2,minmax(0,1fr)); gap:12px; align-items:start; }
  [data-testid="stMarkdownContainer"]:has(> details.m4-card) > details.m4-card{ margin-bottom:0; }
  [data-testid="stTextInput"], [data-testid="stSelectbox"], [data-testid="stDateInput"], [data-testid="stTextArea"]{ max-width:620px; }
  [data-testid="stTabs"] [role="tablist"]{ gap:6px; }
  .m4-mx-wrap{ max-width:100%; }
  table.m4-mx{ font-size:.8rem; }
  .m4-mx th, .m4-mx td{ padding:.5rem .8rem; }
  [data-testid="stPopover"]{ right:1.9rem; }
  table.m4-mx.m4-ab th, table.m4-mx.m4-ab td, table.m4-mx.m4-chg th, table.m4-mx.m4-chg td, table.m4-mx.m4-ctl th, table.m4-mx.m4-ctl td{
    font-size:.82rem !important; padding:.5rem .9rem !important; }
  table.m4-mx.m4-ab th, table.m4-mx.m4-chg th, table.m4-mx.m4-ctl th{ font-size:.68rem !important; }
  .m4-copy{ margin-top:2rem; }
}
</style>"""



def injecter_ergonomie_js():
    import streamlit.components.v1 as components
    components.html('''<script>
    (function(){
      const doc = window.parent.document;
      function appliquer(){
        // Clavier numérique adapté pour les champs DF10 / séquences
        doc.querySelectorAll('input[type="text"], textarea').forEach(el => {
          const ph = (el.placeholder || "").toLowerCase();
          const ar = (el.getAttribute("aria-label") || "").toLowerCase();
          if(ph.includes("54756") || ph.includes("457") || ph.includes("1102") || ar.includes("séquence") || ar.includes("df10")){
            el.setAttribute("inputmode", "decimal");
          }
        });
      }
      appliquer();
      const obs = new MutationObserver(appliquer);
      obs.observe(doc.body, {childList:true, subtree:true});
    })();
    </script>''', height=0)

def main():
    if "utilisateur" not in st.session_state and not restaurer_session():
        ecran_connexion()
        return
    if not reveiller_base():
        return
    if jeton := st.session_state.pop("_poser_cookie", ""):
        st.html(JS_POSER_COOKIE.replace("__J__", jeton), unsafe_allow_javascript=True)
    if "_prefs_ok" not in st.session_state:
        charger_preferences(st.session_state["utilisateur"]["id"])
    st.markdown(CSS.replace("__ENTETE__", arts()["entete"]) + CSS_FOND.replace("__FOND__", url_fond())
                + css_apparence() + CSS_PC, unsafe_allow_html=True)      # thème et fond d'abord : le reste s'affiche déjà habillé
    try:
        n_alertes = sum(1 for a in charger_alertes([], []) if a["niveau"] == "rouge") if droits()["alertes"] else 0
    except Exception:
        n_alertes = 0   # table « permis » absente en ligne : la fenêtre l'explique
    admin = est_admin()
    if n_alertes:       # point rouge sur la cloche (st.html : aucun espace ajouté à la page)
        st.html("<style>.st-key-barre_actions .st-key-btn_alertes button::after{ content:\"\"; position:absolute; top:5px; right:5px; "
                "width:10px; height:10px; border-radius:50%; background:#E5484D; border:2px solid var(--bg); "
                "box-shadow:0 0 0 1px rgba(229,72,77,.45); }</style>")
    titre, essence = [], []
    d = droits()
    with st.container(key="barre_actions"):
        cols_top = st.columns(int(bool(d["alertes"])) + int(bool(admin)) + int(bool(d["partage"])) + 1)
        k = 0
        if d["alertes"]:
            with cols_top[k]:
                if st.button("Alertes", icon=":material/notifications:", key="btn_alertes",
                             help=f"Alertes ({n_alertes} en cours)" if n_alertes else "Alertes : aucune en cours"):
                    dialogue_alertes()
            k += 1
        if admin:
            with cols_top[k]:
                if st.button("Journal", icon=":material/history:", key="btn_journal", help="Journal d'activité"):
                    dialogue_journal()   # réservé aux administrateurs
            k += 1
        if d["partage"]:
            with cols_top[k]:
                if st.button("Partager", icon=":material/ios_share:", key="btn_partage", help="Partager"):
                    st.session_state["pt_titres"], st.session_state["pt_ess"] = filtres_globaux()   # préremplis avec les filtres actifs
                    dialogue_partage()
            k += 1
        with cols_top[k]:
            with st.popover("Réglages", icon=":material/settings:", help="Réglages"):
                st.markdown(f'<div class="m4-reg-nom">{e(st.session_state["utilisateur"]["nom"])}</div>'
                            f'<div class="m4-sec" style="margin:.1rem 0 0">{e(LIBELLES_ROLES[role_actuel()])}</div>', unsafe_allow_html=True)
                st.markdown('<div class="m4-sec" style="margin-top:.3rem">Apparence</div>', unsafe_allow_html=True)
                seg("Thème", THEMES, key="theme", label_visibility="collapsed")
                seg("Taille du texte", list(TAILLES), key="taille", label_visibility="collapsed",
                    help="A− petit · A normal · A+ grand · A++ très grand")
                enregistrer_preferences()
                st.slider("Seuil d'alerte de perte (%)", 1, 50, 10, key="seuil",
                          help="Au-delà de ce pourcentage de perte, la grume est marquée « Perte élevée » dans sa fiche.")
                b1, b2 = st.columns(2)
                if b1.button("Actualiser", width="stretch"):
                    st.cache_data.clear()
                    st.rerun()
                if b2.button("Se déconnecter", width="stretch"):
                    noter(st.session_state["utilisateur"]["id"], "deconnexion")
                    oublier_session()
                    st.session_state.clear()
                    st.rerun()
    injecter_ergonomie_js()
    entete()
    if d["filtres"]:
        with st.expander("Filtres : titre, site, essence"):
            try:
                titres, essences = listes_filtres()
            except Exception:
                titres, essences = [], []
            titre = st.multiselect("Titre(s)", titres, key="ft", placeholder="Tous les titres")
            sites_dispo = liste_sites()
            if sites_dispo:
                st.multiselect("Site(s)", sites_dispo + [SANS_SITE], key="fs", placeholder="Tous les sites",
                               help="Agit sur l'évacué, l'usiné et le stock du site (indicateurs du haut et bilan). L'abattu, l'exploité et l'abandon ne dépendent pas du site.")
            essence = st.multiselect("Essence(s)", essences, key="fe", placeholder="Toutes les essences")
    seuil = st.session_state.get("seuil", 10) / 100.0

    noms = d["onglets"]
    zones = dict(zip(noms, st.tabs(noms)))
    try:
        if "Aperçu" in zones or "Rapports" in zones:
            donnees = filtrer(charger_donnees(), titre, essence)
            evacs = filtrer(charger_evac(), titre, essence)
        if "Aperçu" in zones:
            with zones["Aperçu"]:
                if est_admin() and (n_dem := len(demandes_en_attente())):
                    st.markdown(f'<div class="m4-banniere">🔑 {n_dem} demande(s) de mot de passe en attente — ouvrez le journal '
                                f'(pastille en haut) puis « Demandes ».</div>', unsafe_allow_html=True)
                if n_alertes and d["alertes"]:
                    st.markdown(f'<div class="m4-banniere">⚠ {n_alertes} dépassement(s) du permis — touchez la pastille ⚠ en haut.</div>',
                                unsafe_allow_html=True)
                vue_apercu(donnees, evacs, titre, essence)
        if "Abattage" in zones:
            with zones["Abattage"]:
                vue_abattage(titre, essence)
        if "Carte" in zones:
            with zones["Carte"]:
                vue_carte(titre)
        if "Rapports" in zones:
            with zones["Rapports"]:
                vue_rapports(donnees, evacs, titre, essence)
        if "Rechercher" in zones:
            with zones["Rechercher"]:
                vue_recherche(seuil)
        if "Chargement" in zones:
            with zones["Chargement"]:
                vue_chargement()
    except psycopg2.errors.InsufficientPrivilege as exc:
        journal.exception("Droits insuffisants sur la base")
        st.error("La base en ligne est joignable, mais l'accès à une table est refusé (" + str(exc).strip().splitlines()[0]
                 + "). Il faut redonner le droit de lecture au compte de l'application — voir l'administrateur de la base.")
    except psycopg2.Error:
        journal.exception("Erreur base de données")
        st.error("La base en ligne ne répond pas pour le moment. Réessayez dans un instant.")
    st.markdown('<div class="m4-copy clair">© Ngapout Mbarga Michel Mohamed 2026</div>', unsafe_allow_html=True)


main()
