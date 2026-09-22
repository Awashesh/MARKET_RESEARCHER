#!/usr/bin/env python3
"""
Indian Stock & Mutual Fund Screener  (colourful GUI + live prices + interactive charts)
========================================================================================

Open the GUI (just run with no arguments):

    python market_screener.py

Install once:

    pip install yfinance pandas numpy requests
    (Tkinter comes with Python on Windows/Mac. On Linux: sudo apt install python3-tk)

GUI tabs
--------
1. Stocks Screener      : Top-N shares from Nifty 50 / Midcap 150 / Smallcap 250 ranked by
                          1M / 2M / 6M / 1Y / 3Y / 5Y return + minimum growth filter (10/20/50%).
2. Mutual Funds Screener: Top-N mutual funds (scan a few or ALL matching schemes).
3. Search Equity / Fund : Search ANY listed stock or ANY mutual fund (full list, no limit).
                          Names POP UP while you type (auto-suggest) - pick one to open it.
                          Shows returns, risk, dividends, news and a LIVE price while NSE is open.
4. Chart                : Big full-size chart of whatever you searched. Move the mouse over it
                          to see the exact date and price.
5. Live Watchlist       : Auto-refreshing live prices (indices + your own stocks).

Chart options (available everywhere you see a chart)
----------------------------------------------------
  * Chart tab         - big chart inside the app
  * Pop-out window    - separate resizable / full-screen window (F11)
  * Open in browser   - interactive HTML chart (works offline, hover for date & price)
  * Click any stock / fund NAME in the screener tables to pop out its chart.
  Ranges: 1D (live intraday) 5D 1M 6M 1Y 3Y 5Y MAX.

Live prices: Yahoo Finance data, refreshed every few seconds while the market is open
(NSE: Mon-Fri 09:15-15:30 IST). It can be delayed by a short time; exchange holidays are not
detected. Mutual fund NAV is declared once a day, so it cannot be "live".

Command-line examples (optional)
--------------------------------
    python market_screener.py stocks --universe all --period 6m --min-growth 20 --top 10
    python market_screener.py funds  --query "small cap" --period 1y --top 10 --max-funds 0
    (--max-funds 0 = scan ALL matching schemes)

DISCLAIMER: Educational tool only. Not investment advice. Past performance
does not guarantee future returns. Always do your own research.
"""

import argparse
import html
import io
import json
import os
import re
import sys
import tempfile
import time
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone, time as dtime
from pathlib import Path
from urllib.parse import quote_plus

import numpy as np
import pandas as pd
import requests
import yfinance as yf

# --------------------------------------------------------------------------
# CONFIG
# --------------------------------------------------------------------------
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
    )
}

INDEX_URLS = {
    "nifty50": "https://archives.nseindia.com/content/indices/ind_nifty50list.csv",
    "midcap": "https://archives.nseindia.com/content/indices/ind_niftymidcap150list.csv",
    "smallcap": "https://archives.nseindia.com/content/indices/ind_niftysmallcap250list.csv",
}

# Small backup lists, used only if the NSE download fails.
FALLBACK = {
    "nifty50": [
        "RELIANCE", "TCS", "HDFCBANK", "INFY", "ICICIBANK", "ITC", "LT", "SBIN",
        "BHARTIARTL", "AXISBANK", "KOTAKBANK", "HINDUNILVR", "MARUTI",
        "SUNPHARMA", "TITAN", "NTPC", "ONGC", "TATASTEEL", "WIPRO", "HCLTECH",
    ],
    "midcap": [
        "PERSISTENT", "MPHASIS", "VOLTAS", "POLYCAB", "TVSMOTOR", "BHARATFORG",
        "INDHOTEL", "ASHOKLEY", "MUTHOOTFIN", "LUPIN", "FEDERALBNK", "COFORGE",
    ],
    "smallcap": [
        "CDSL", "ANGELONE", "CASTROLIND", "KPITTECH", "REDINGTON", "RBLBANK",
        "BSE", "CESC", "NATIONALUM", "IEX",
    ],
}

# Look-back windows (calendar based)
PERIODS = {
    "1m": pd.DateOffset(months=1),
    "2m": pd.DateOffset(months=2),
    "6m": pd.DateOffset(months=6),
    "1y": pd.DateOffset(years=1),
    "3y": pd.DateOffset(years=3),
    "5y": pd.DateOffset(years=5),
}

NEGATIVE_WORDS = [
    "fraud", "probe", "penalty", "penalised", "fine", "fined", "downgrade",
    "downgrades", "downgraded", "loss", "losses", "default", "lawsuit", "sebi",
    "ban", "banned", "raid", "raids", "resigns", "resignation", "slump",
    "slumps", "plunge", "plunges", "crash", "crashes", "falls", "fall", "drops",
    "tumbles", "slides", "sinks", "decline", "declines", "weak", "misses",
    "miss", "cut", "cuts", "warning", "warns", "concern", "concerns",
    "investigation", "scam", "debt", "bankruptcy", "insolvency", "sell",
    "underperform", "pledge", "shortfall", "recall", "shutdown", "strike",
    "no dividend", "skips dividend", "dividend cut",
]
POSITIVE_WORDS = [
    "profit", "profits", "surge", "surges", "jumps", "rallies", "rally",
    "gains", "gain", "upgrade", "upgrades", "upgraded", "record", "beats",
    "wins", "order win", "bags", "buy", "outperform", "growth", "dividend",
    "bonus", "expansion", "strong", "soars", "rises", "climbs", "target",
]
NEG_RE = re.compile(r"\b(" + "|".join(map(re.escape, NEGATIVE_WORDS)) + r")\b", re.I)
POS_RE = re.compile(r"\b(" + "|".join(map(re.escape, POSITIVE_WORDS)) + r")\b", re.I)

WATCH_FILE = os.path.join(os.path.expanduser("~"), ".market_screener_watchlist.json")
DEFAULT_WATCH = [
    {"ticker": "^NSEI", "name": "NIFTY 50"}, {"ticker": "^NSEBANK", "name": "NIFTY BANK"},
    {"ticker": "^BSESN", "name": "SENSEX"}, {"ticker": "RELIANCE.NS", "name": "RELIANCE"},
    {"ticker": "TCS.NS", "name": "TCS"}, {"ticker": "HDFCBANK.NS", "name": "HDFCBANK"},
    {"ticker": "INFY.NS", "name": "INFY"}, {"ticker": "ICICIBANK.NS", "name": "ICICIBANK"},
    {"ticker": "SBIN.NS", "name": "SBIN"},
]


class ScreenerError(Exception):
    """Friendly error shown to the user (no traceback)."""


# Progress messages go here. The GUI replaces this to show them on screen.
LOGGER = print


def log(msg: str):
    LOGGER(msg)


# --------------------------------------------------------------------------
# MARKET CLOCK (NSE: Mon-Fri 09:15-15:30 IST)
# --------------------------------------------------------------------------
IST = timezone(timedelta(hours=5, minutes=30))


def ist_now() -> datetime:
    return datetime.now(timezone.utc).astimezone(IST)


def is_market_open(now: datetime = None) -> bool:
    """True during NSE trading hours (exchange holidays are not detected)."""
    now = now or ist_now()
    if now.weekday() >= 5:
        return False
    return dtime(9, 15) <= now.time() <= dtime(15, 30)


# --------------------------------------------------------------------------
# HELPERS: RETURNS & RISK
# --------------------------------------------------------------------------
def pct_return(series: pd.Series, offset: pd.DateOffset) -> float:
    """% change between (last date - offset) and last date."""
    s = series.dropna()
    if s.empty:
        return np.nan
    end = s.index[-1]
    start = end - offset
    if s.index[0] > start + pd.Timedelta(days=7):  # not enough history
        return np.nan
    past = s.loc[:start]
    base = past.iloc[-1] if not past.empty else s.iloc[0]
    return (s.iloc[-1] / base - 1) * 100


def risk_metrics(series: pd.Series) -> dict:
    """1-year annualised volatility and max drawdown (in %)."""
    s = series.dropna()
    if len(s) < 30:
        return {"Volatility_1y_%": np.nan, "MaxDrawdown_1y_%": np.nan}
    last_year = s[s.index >= s.index[-1] - pd.DateOffset(years=1)]
    vol = last_year.pct_change().std() * np.sqrt(252) * 100
    dd = (last_year / last_year.cummax() - 1).min() * 100
    return {"Volatility_1y_%": round(vol, 1), "MaxDrawdown_1y_%": round(dd, 1)}


def cagr(total_return_pct: float, years: int) -> float:
    if pd.isna(total_return_pct):
        return np.nan
    return round(((1 + total_return_pct / 100) ** (1 / years) - 1) * 100, 2)


def returns_row(s: pd.Series) -> dict:
    row = {f"Ret_{label}_%": round(pct_return(s, off), 2) for label, off in PERIODS.items()}
    row["CAGR_3y_%"] = cagr(row["Ret_3y_%"], 3)
    row["CAGR_5y_%"] = cagr(row["Ret_5y_%"], 5)
    return row


def range_stats(s: pd.Series) -> dict:
    """52-week high/low, distance from high and last-day change."""
    y = s[s.index >= s.index[-1] - pd.DateOffset(years=1)]
    hi, lo, last = float(y.max()), float(y.min()), float(s.iloc[-1])
    day = round((last / float(s.iloc[-2]) - 1) * 100, 2) if len(s) > 1 else np.nan
    return {"High_52w": round(hi, 2), "Low_52w": round(lo, 2),
            "From_High_%": round((last / hi - 1) * 100, 2), "Day_%": day}


def compute_buckets(df: pd.DataFrame, col: str, name_col: str) -> dict:
    """Names of stocks/funds that grew >= 10%, 20%, 50% in the chosen period."""
    return {th: df.loc[df[col] >= th, name_col].tolist() for th in (10, 20, 50)}


# --------------------------------------------------------------------------
# STOCK UNIVERSE & PRICES
# --------------------------------------------------------------------------
def load_index(name: str) -> pd.DataFrame:
    label = {"nifty50": "Nifty 50", "midcap": "Midcap 150", "smallcap": "Smallcap 250"}[name]
    try:
        r = requests.get(INDEX_URLS[name], headers=HEADERS, timeout=30)
        r.raise_for_status()
        df = pd.read_csv(io.StringIO(r.text)).rename(columns={"Company Name": "Company"})
        df = df[["Symbol", "Company", "Industry"]].copy()
    except Exception as e:  # noqa: BLE001
        log(f"[warn] Could not download {label} list from NSE ({e}). Using small backup list.")
        df = pd.DataFrame({"Symbol": FALLBACK[name]})
        df["Company"] = df["Symbol"]
        df["Industry"] = ""
    df["Category"] = label
    return df


def get_universe(name: str) -> pd.DataFrame:
    names = ["nifty50", "midcap", "smallcap"] if name == "all" else [name]
    uni = pd.concat([load_index(n) for n in names], ignore_index=True)
    return uni.drop_duplicates(subset="Symbol").reset_index(drop=True)


_UNIVERSE_CACHE = None


def cached_universe() -> pd.DataFrame:
    """All Nifty 50 + Midcap + Smallcap stocks (downloaded once, then cached)."""
    global _UNIVERSE_CACHE
    if _UNIVERSE_CACHE is None:
        _UNIVERSE_CACHE = get_universe("all")
    return _UNIVERSE_CACHE


def download_prices(symbols, years: int = 5) -> pd.DataFrame:
    """Adjusted close prices (Yahoo Finance uses the .NS suffix for NSE)."""
    tickers = [f"{s}.NS" for s in symbols]
    frames = []
    for i in range(0, len(tickers), 100):
        chunk = tickers[i:i + 100]
        log(f"Downloading prices {i + 1}-{i + len(chunk)} of {len(tickers)} ...")
        try:
            raw = yf.download(chunk, period=f"{years}y", interval="1d",
                              auto_adjust=True, progress=False, threads=True)
        except Exception as e:  # noqa: BLE001
            log(f"[warn] price download failed for a batch: {e}")
            continue
        if raw is None or raw.empty:
            continue
        close = raw["Close"]
        if isinstance(close, pd.Series):
            close = close.to_frame(chunk[0])
        frames.append(close)
    if not frames:
        raise ScreenerError("No price data downloaded. Please check your internet connection.")
    prices = pd.concat(frames, axis=1).dropna(axis=1, how="all")
    prices.index = pd.to_datetime(prices.index).tz_localize(None)
    return prices.sort_index()


def build_stock_table(prices: pd.DataFrame, uni: pd.DataFrame) -> pd.DataFrame:
    rows = []
    for tick in prices.columns:
        s = prices[tick].dropna()
        if len(s) < 30:
            continue
        row = {"Symbol": tick.replace(".NS", ""), "Price": round(float(s.iloc[-1]), 2)}
        for label, off in PERIODS.items():
            row[f"Ret_{label}_%"] = round(pct_return(s, off), 2)
        row.update(risk_metrics(s))
        rows.append(row)
    df = pd.DataFrame(rows)
    if df.empty:
        return df
    return df.merge(uni[["Symbol", "Company", "Industry", "Category"]], on="Symbol", how="left")


def _close_series(raw) -> pd.Series:
    """Single tz-naive 'Close' Series from a yfinance download result."""
    close = raw["Close"]
    if isinstance(close, pd.DataFrame):
        close = close.iloc[:, 0]
    close = close.dropna()
    close.index = pd.to_datetime(close.index).tz_localize(None)
    return close


# --------------------------------------------------------------------------
# LIVE PRICES + INTRADAY
# --------------------------------------------------------------------------
def fetch_intraday(ticker: str, span: str = "1D"):
    """Intraday prices. '1D' = last trading day (1-minute), '5D' = last 5 days (15-minute)."""
    interval = "1m" if span == "1D" else "15m"
    raw = yf.download(ticker, period="5d", interval=interval, auto_adjust=True, progress=False)
    if raw is None or raw.empty:
        return None
    close = _close_series(raw)
    if span == "1D" and len(close):
        close = close[close.index.date == close.index[-1].date()]
    return close if len(close) > 1 else None


def _fast(fi, key):
    try:
        v = float(getattr(fi, key))
    except Exception:  # noqa: BLE001
        return None
    return None if np.isnan(v) else v


def fetch_live_quote(ticker: str) -> dict:
    """Latest (near real-time) price of a stock / index."""
    price = prev = hi = lo = vol = None
    try:
        fi = yf.Ticker(ticker).fast_info
        price, prev, hi, lo, vol = (_fast(fi, k) for k in
                                    ("last_price", "previous_close", "day_high", "day_low", "last_volume"))
    except Exception:  # noqa: BLE001
        pass
    if price is None:  # fall back to the latest 1-minute candle
        ser = fetch_intraday(ticker, "1D")
        if ser is not None:
            price, hi, lo = float(ser.iloc[-1]), float(ser.max()), float(ser.min())
    if price is None:
        raise ScreenerError(f"No live price found for {ticker}.")
    if prev is None:
        try:
            d = _close_series(yf.download(ticker, period="5d", interval="1d",
                                          auto_adjust=True, progress=False))
            prev = float(d.iloc[-2]) if len(d) > 1 else price
        except Exception:  # noqa: BLE001
            prev = price
    change = price - prev
    return {"ticker": ticker, "price": price, "prev_close": prev, "change": change,
            "pct": (change / prev * 100) if prev else 0.0, "high": hi, "low": lo, "volume": vol,
            "time": datetime.now().strftime("%H:%M:%S"), "open": is_market_open()}


def fetch_many_quotes(tickers) -> dict:
    """Live quotes for many tickers in parallel -> {ticker: quote or {'error': msg}}."""
    def one(t):
        try:
            return t, fetch_live_quote(t)
        except Exception as e:  # noqa: BLE001
            return t, {"error": str(e)}
    with ThreadPoolExecutor(max_workers=6) as ex:
        return dict(ex.map(one, tickers))


def load_watchlist() -> list:
    try:
        with open(WATCH_FILE, encoding="utf-8") as f:
            items = json.load(f)
        if isinstance(items, list) and items:
            return [i for i in items if isinstance(i, dict) and "ticker" in i]
    except Exception:  # noqa: BLE001
        pass
    return [dict(i) for i in DEFAULT_WATCH]


def save_watchlist(items: list):
    try:
        with open(WATCH_FILE, "w", encoding="utf-8") as f:
            json.dump(items, f, indent=1)
    except Exception:  # noqa: BLE001
        pass


def fmt_volume(v) -> str:
    if v is None or not _isnum(v) or float(v) <= 0:
        return "-"
    v = float(v)
    return f"{v / 1e7:.2f} Cr" if v >= 1e7 else f"{v / 1e5:.2f} L" if v >= 1e5 else f"{v:,.0f}"


# --------------------------------------------------------------------------
# DIVIDENDS
# --------------------------------------------------------------------------
def get_dividend_series(ticker: str):
    """Dividend history (Series) - None if it could not be fetched."""
    try:
        div = yf.Ticker(ticker).dividends
    except Exception:  # noqa: BLE001
        return None
    if div is None:
        return None
    if not div.empty:
        div = div.copy()
        div.index = pd.to_datetime(div.index).tz_localize(None)
    return div


def dividend_summary(div, price: float) -> dict:
    """Dividend yield + whether dividends are growing, stable, cut or stopped."""
    empty = {"Div_12M_Rs": 0.0, "Div_Yield_%": 0.0, "Div_Trend": "No dividend", "Last_Div_Date": ""}
    if div is None:
        return {**empty, "Div_Trend": "Unknown"}
    if div.empty:
        return empty

    now = pd.Timestamp.today().normalize()
    last12 = float(div[div.index > now - pd.DateOffset(years=1)].sum())
    prev12 = float(div[(div.index > now - pd.DateOffset(years=2))
                       & (div.index <= now - pd.DateOffset(years=1))].sum())

    if last12 == 0 and prev12 > 0:
        trend = "STOPPED (negative)"
    elif last12 == 0:
        trend = "No recent dividend"
    elif prev12 == 0:
        trend = "New payer"
    elif last12 < prev12 * 0.9:
        trend = "CUT (negative)"
    elif last12 > prev12 * 1.1:
        trend = "Growing"
    else:
        trend = "Stable"

    return {
        "Div_12M_Rs": round(last12, 2),
        "Div_Yield_%": round(last12 / price * 100, 2) if price else 0.0,
        "Div_Trend": trend,
        "Last_Div_Date": div.index[-1].strftime("%Y-%m-%d"),
    }


def dividend_info(symbol: str, price: float) -> dict:
    return dividend_summary(get_dividend_series(f"{symbol}.NS"), price)


# --------------------------------------------------------------------------
# NEWS (Google News RSS - no API key needed)
# --------------------------------------------------------------------------
def news_items(name: str, topic: str = "share", max_items: int = 15) -> list:
    """Headlines of the last 30 days: [{'title','date','link','tone'}]. tone = neg/pos/neu."""
    clean = re.sub(r"\b(ltd|limited|inc|corp|corporation)\b\.?", "", name, flags=re.I).strip()
    q = quote_plus(f"{clean} {topic} when:30d")
    url = f"https://news.google.com/rss/search?q={q}&hl=en-IN&gl=IN&ceid=IN:en"
    try:
        r = requests.get(url, headers=HEADERS, timeout=20)
        r.raise_for_status()
        root = ET.fromstring(r.content)
        out = []
        for it in root.findall("./channel/item")[:max_items]:
            title = it.findtext("title", "")
            n, p = len(NEG_RE.findall(title)), len(POS_RE.findall(title))
            out.append({"title": title, "date": it.findtext("pubDate", ""),
                        "link": it.findtext("link", ""),
                        "tone": "neg" if n > p else "pos" if p > n else "neu"})
        return out
    except Exception:  # noqa: BLE001
        return []


def sentiment_from_items(items: list) -> dict:
    neg = [i["title"] for i in items if i["tone"] == "neg"]
    pos = [i for i in items if i["tone"] == "pos"]
    if not items:
        flag = "No news found"
    elif len(neg) >= 3 and len(neg) > len(pos):
        flag = "NEGATIVE"
    elif len(neg) > len(pos):
        flag = "Mildly negative"
    elif len(pos) > len(neg):
        flag = "Positive"
    else:
        flag = "Neutral"
    return {"News_Count": len(items), "News_Neg": len(neg), "News_Pos": len(pos),
            "News_Flag": flag, "Negative_Headlines": " || ".join(neg[:3])}


def news_sentiment(name: str, topic: str = "share") -> dict:
    return sentiment_from_items(news_items(name, topic))


def fund_search_name(name: str) -> str:
    """'Nippon India Small Cap Fund - Direct Plan - Growth' -> 'Nippon India Small Cap Fund'."""
    clean = re.sub(r"\b(direct|regular|plan|growth|option|idcw|dividend|payout|reinvestment)\b",
                   " ", name, flags=re.I)
    return re.sub(r"[-\u2013()]+", " ", clean).split("  ")[0].strip() or name


# --------------------------------------------------------------------------
# RED FLAGS & SIGNAL
# --------------------------------------------------------------------------
def red_flags(row) -> str:
    flags = []
    if "negative" in str(row.get("Div_Trend", "")).lower():
        flags.append("DIVIDEND")
    if row.get("News_Flag") in ("NEGATIVE", "Mildly negative"):
        flags.append("NEWS")
    dd, vol = row.get("MaxDrawdown_1y_%"), row.get("Volatility_1y_%")
    if dd is not None and pd.notna(dd) and dd <= -35:
        flags.append("BIG-DRAWDOWN")
    if vol is not None and pd.notna(vol) and vol >= 55:
        flags.append("HIGH-VOLATILITY")
    return ", ".join(flags) if flags else "-"


def signal_score(row) -> int:
    """+1 per positive period (1M,2M,6M,1Y), +1 if 6M >= 20%, -1 per red flag."""
    score = 0
    for p in ("1m", "2m", "6m", "1y"):
        v = row.get(f"Ret_{p}_%")
        if v is not None and pd.notna(v):
            score += 1 if v > 0 else -1
    v6 = row.get("Ret_6m_%")
    if v6 is not None and pd.notna(v6) and v6 >= 20:
        score += 1
    rf = str(row.get("Red_Flags", "-"))
    if rf not in ("-", "", "nan"):
        score -= len(rf.split(", "))
    return score


def score_label(score: int) -> str:
    return "STRONG" if score >= 4 else "GOOD" if score >= 2 else "WATCH" if score >= 0 else "AVOID"


def add_signal(df: pd.DataFrame) -> pd.DataFrame:
    df["Red_Flags"] = df.apply(red_flags, axis=1)
    df["Score"] = df.apply(signal_score, axis=1)
    df["Signal"] = df["Score"].map(score_label)
    return df


# --------------------------------------------------------------------------
# COLOUR HELPERS (pure python - used by the GUI heat-map)
# --------------------------------------------------------------------------
def _rgb(c: str):
    c = c.lstrip("#")
    return tuple(int(c[i:i + 2], 16) for i in (0, 2, 4))


def mix(c1: str, c2: str, t: float) -> str:
    a, b = _rgb(c1), _rgb(c2)
    return "#%02x%02x%02x" % tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


NEUTRAL = ("#eceff1", "#607d8b")
RET_SCALE = {"1m": 15, "2m": 20, "6m": 40, "1y": 60, "3y": 120, "5y": 200}
GREEN, AMBER, RED = ("#c8efd4", "#14532d"), ("#ffe8b3", "#7a4b00"), ("#f8c9c9", "#8b1a1a")

BADGES = {
    "Signal": {"STRONG": ("#1b7f3b", "#ffffff"), "GOOD": ("#5cb85c", "#ffffff"),
               "WATCH": ("#f0ad4e", "#222222"), "AVOID": ("#d9534f", "#ffffff")},
    "Category": {"Nifty 50": ("#d6e6ff", "#0b3d91"), "Midcap 150": ("#ead9ff", "#5b2a86"),
                 "Smallcap 250": ("#ffe5cc", "#8a4b08")},
    "News_Flag": {"Positive": GREEN, "Neutral": NEUTRAL, "Mildly negative": AMBER,
                  "NEGATIVE": RED, "No news found": NEUTRAL},
    "Div_Trend": {"Growing": GREEN, "New payer": ("#d1f2eb", "#0e6251"),
                  "Stable": ("#d9ecff", "#0b3d91"), "No dividend": NEUTRAL,
                  "No recent dividend": NEUTRAL, "Unknown": NEUTRAL,
                  "CUT (negative)": RED, "STOPPED (negative)": RED},
}


def _isnum(v) -> bool:
    try:
        return v is not None and not pd.isna(float(v))
    except (TypeError, ValueError):
        return False


def return_style(v, scale: float):
    """Green for gains, red for losses - colour gets deeper with size."""
    if not _isnum(v):
        return NEUTRAL
    v = float(v)
    t = min(abs(v) / scale, 1.0)
    bg = mix("#e6f6ea", "#1f9d55", t) if v >= 0 else mix("#fdeaea", "#d93b3b", t)
    return bg, ("#ffffff" if t > 0.6 else "#1b1b1b")


def cell_style(col: str, v):
    """-> (text, background, foreground) for one table cell."""
    plain = ("#ffffff", "#1b1b1b")
    if col.startswith("Ret_") or col.startswith("CAGR_"):
        scale = RET_SCALE.get(col.split("_")[1], 30) if col.startswith("Ret_") else 30
        bg, fg = return_style(v, scale)
        txt = f"{'▲' if float(v) >= 0 else '▼'} {float(v):.2f}" if _isnum(v) else "-"
        return txt, bg, fg
    if col in ("Volatility_1y_%", "MaxDrawdown_1y_%"):
        if not _isnum(v):
            return ("-",) + NEUTRAL
        v = float(v)
        if col == "Volatility_1y_%":
            bg, fg = GREEN if v < 25 else AMBER if v < 40 else RED
        else:
            bg, fg = GREEN if v > -15 else AMBER if v > -30 else RED
        return f"{v:.1f}%", bg, fg
    if col == "Div_Yield_%":
        if not _isnum(v):
            return ("-",) + NEUTRAL
        v = float(v)
        bg, fg = (("#8fd6a7", "#0b3d1e") if v >= 2 else GREEN if v >= 0.5
                  else ("#e6f6ea", "#2e7d32") if v > 0 else NEUTRAL)
        return f"{v:.2f}%", bg, fg
    if col == "Red_Flags":
        if str(v) in ("-", "", "nan", "None"):
            return ("✔ Clear", "#e6f6ea", "#1b7f3b")
        return ("⚠ " + str(v), "#f8c9c9", "#8b1a1a")
    if col in BADGES:
        bg, fg = BADGES[col].get(str(v), NEUTRAL)
        return str(v), bg, fg
    if col in ("Price", "NAV") and _isnum(v):
        return f"{float(v):,.2f}", plain[0], plain[1]
    return ("" if v is None else str(v)), plain[0], plain[1]


PRETTY = {
    "Ret_1m_%": "1M %", "Ret_2m_%": "2M %", "Ret_6m_%": "6M %", "Ret_1y_%": "1Y %",
    "Ret_3y_%": "3Y %", "Ret_5y_%": "5Y %", "CAGR_3y_%": "3Y CAGR %", "CAGR_5y_%": "5Y CAGR %",
    "Volatility_1y_%": "Volatility 1Y", "MaxDrawdown_1y_%": "Max Drop 1Y",
    "Div_Yield_%": "Div Yield", "Div_Trend": "Dividend Trend", "News_Flag": "News Mood",
    "Red_Flags": "Red Flags", "Price": "Price (Rs)", "NAV": "NAV (Rs)",
}
COLW = {"Symbol": 13, "Company": 27, "Category": 13, "Signal": 9, "Price": 11, "Fund": 55,
        "NAV": 10, "Div_Trend": 19, "News_Flag": 15, "Red_Flags": 32, "Div_Yield_%": 10,
        "Volatility_1y_%": 12, "MaxDrawdown_1y_%": 12, "CAGR_3y_%": 10, "CAGR_5y_%": 10}
LEFT_COLS = {"Symbol", "Company", "Fund"}


def pretty(col: str) -> str:
    return PRETTY.get(col, col.replace("_", " "))


# --------------------------------------------------------------------------
# CORE: STOCK SCREEN  (used by both GUI and command line)
# --------------------------------------------------------------------------
def screen_stocks(universe="all", period="6m", min_growth=None, top=10,
                  consistent=False, news=True, dividends=True):
    col = f"Ret_{period}_%"
    log(f"Universe: {universe} | ranking by {period.upper()} return")
    uni = get_universe(universe)
    log(f"Universe size: {len(uni)} stocks")
    prices = download_prices(uni["Symbol"].tolist(), years=5)
    df = build_stock_table(prices, uni)
    if df.empty:
        raise ScreenerError("No price data could be analysed.")

    df = df.dropna(subset=[col])
    buckets = compute_buckets(df, col, "Symbol")

    if consistent:
        df = df[(df["Ret_1m_%"] > 0) & (df["Ret_2m_%"] > 0) & (df["Ret_6m_%"] > 0)]
        log(f"After 'consistent' filter (positive in 1M, 2M, 6M): {len(df)} stocks")
    if min_growth is not None:
        df = df[df[col] >= min_growth]
        log(f"After min growth >= {min_growth}% filter: {len(df)} stocks")

    df = df.sort_values(col, ascending=False).head(top).reset_index(drop=True)
    if df.empty:
        raise ScreenerError("No stock passed your filters. Try a lower minimum growth.")

    if dividends:
        log("Fetching dividend history ...")
        divs = [dividend_info(r.Symbol, r.Price) for r in df.itertuples()]
        df = pd.concat([df, pd.DataFrame(divs)], axis=1)

    if news:
        log("Fetching latest news ...")
        rows = []
        for i, r in enumerate(df.itertuples(), 1):
            log(f"News {i}/{len(df)}: {r.Symbol}")
            rows.append(news_sentiment(r.Company if isinstance(r.Company, str) else r.Symbol))
            time.sleep(0.5)  # be polite to the server
        df = pd.concat([df, pd.DataFrame(rows)], axis=1)

    return add_signal(df), buckets


# --------------------------------------------------------------------------
# CORE: MUTUAL FUND SCREEN  (data: https://www.mfapi.in - free AMFI NAV API)
# --------------------------------------------------------------------------
MF_SEARCH = "https://api.mfapi.in/mf/search"
MF_NAV = "https://api.mfapi.in/mf/{}"


def search_funds(query: str) -> list:
    r = requests.get(MF_SEARCH, params={"q": query}, headers=HEADERS, timeout=30)
    r.raise_for_status()
    return r.json()


def fetch_fund(code):
    """NAV history (Series) and meta info (dict) of one scheme."""
    r = requests.get(MF_NAV.format(code), headers=HEADERS, timeout=30)
    r.raise_for_status()
    j = r.json()
    data = pd.DataFrame(j.get("data", []))
    if data.empty:
        return pd.Series(dtype=float), j.get("meta", {}) or {}
    data["date"] = pd.to_datetime(data["date"], format="%d-%m-%Y")
    data["nav"] = data["nav"].astype(float)
    return data.set_index("date")["nav"].sort_index(), j.get("meta", {}) or {}


def fund_nav_series(code) -> pd.Series:
    return fetch_fund(code)[0]


def is_direct_growth(name: str) -> bool:
    n = name.lower()
    return "direct" in n and "growth" in n and not any(
        x in n for x in ("idcw", "dividend", "bonus", "payout", "reinvest"))


def screen_funds(query="flexi cap", period="1y", min_growth=None, top=10,
                 max_funds=40, all_plans=False, news=False):
    """max_funds: how many matching schemes to scan (0 / None = ALL of them)."""
    col = f"Ret_{period}_%"
    log(f"Searching funds for '{query}' ...")
    try:
        funds = search_funds(query)
    except Exception as e:  # noqa: BLE001
        raise ScreenerError(f"Could not reach the mutual fund data service: {e}")
    log(f"Schemes matching search: {len(funds)}")

    if not all_plans:  # keep Direct + Growth plans only
        funds = [f for f in funds if is_direct_growth(f["schemeName"])]
        log(f"After keeping Direct-Growth plans only: {len(funds)}")
    if max_funds:
        funds = funds[:max_funds]
    if not funds:
        raise ScreenerError("No fund found for this search. Try another name.")

    def load(f):
        try:
            return f, fund_nav_series(f["schemeCode"])
        except Exception:  # noqa: BLE001
            return f, None

    rows = []
    log(f"Downloading NAV history of {len(funds)} schemes (8 at a time) ...")
    with ThreadPoolExecutor(max_workers=8) as ex:
        futures = [ex.submit(load, f) for f in funds]
        for i, fut in enumerate(as_completed(futures), 1):
            f, nav = fut.result()
            if i % 10 == 0 or i == len(funds):
                log(f"Downloaded {i}/{len(funds)} schemes ...")
            if nav is None or len(nav) < 30:
                continue
            row = {"Code": f["schemeCode"], "Fund": f["schemeName"], "NAV": round(float(nav.iloc[-1]), 2)}
            row.update(returns_row(nav))
            row.update(risk_metrics(nav))
            rows.append(row)

    df = pd.DataFrame(rows)
    if df.empty:
        raise ScreenerError("No fund data found. Try another search (e.g. 'flexi cap', 'nifty 50 index').")

    df = df.dropna(subset=[col])
    buckets = compute_buckets(df, col, "Fund")
    if min_growth is not None:
        df = df[df[col] >= min_growth]
    df = df.sort_values(col, ascending=False).head(top).reset_index(drop=True)
    if df.empty:
        raise ScreenerError("No fund passed your filters. Try a lower minimum growth.")

    if news:
        log("Fetching news ...")
        rows = [news_sentiment(fund_search_name(n), "mutual fund") for n in df["Fund"]]
        df = pd.concat([df, pd.DataFrame(rows)], axis=1)
    return add_signal(df), buckets


# --------------------------------------------------------------------------
# CORE: SEARCH ANY EQUITY / MUTUAL FUND  (Search tab) - NO result limit
# --------------------------------------------------------------------------
def _equity_candidates(q: str, yahoo_timeout: int = 15) -> list:
    """All stocks whose name / symbol contains the text -> [{'ticker','name','note'}]."""
    results, pos = [], {}

    def add(ticker, name, note):
        if ticker in pos:  # already listed - just upgrade a bare symbol to the full company name
            cur = results[pos[ticker]]
            if name and cur["name"] == ticker.split(".")[0] and name != cur["name"]:
                cur["name"] = name
            return
        pos[ticker] = len(results)
        results.append({"ticker": ticker, "name": name, "note": note})

    # 1) Nifty 50 / Midcap / Smallcap lists (name or symbol contains the text)
    try:
        uni = cached_universe()
        ql = q.lower()
        hit = uni[uni["Symbol"].str.lower().str.contains(re.escape(ql))
                  | uni["Company"].astype(str).str.lower().str.contains(re.escape(ql))]
        for r in hit.itertuples():
            add(f"{r.Symbol}.NS", str(r.Company), str(r.Category))
    except Exception:  # noqa: BLE001
        pass

    # 2) Yahoo Finance search (finds every listed NSE / BSE stock)
    try:
        r = requests.get("https://query2.finance.yahoo.com/v1/finance/search",
                         params={"q": q, "quotesCount": 50, "newsCount": 0, "listsCount": 0},
                         headers=HEADERS, timeout=yahoo_timeout)
        for it in r.json().get("quotes", []):
            sym = it.get("symbol", "")
            if it.get("quoteType") == "EQUITY" and sym.endswith((".NS", ".BO")):
                add(sym, it.get("longname") or it.get("shortname") or sym,
                    "NSE" if sym.endswith(".NS") else "BSE")
    except Exception:  # noqa: BLE001
        pass

    return results


def search_equities(query: str) -> list:
    """Find stocks by name or symbol -> [{'ticker','name','note'}] (all matches)."""
    q = query.strip()
    if not q:
        raise ScreenerError("Type a company name or symbol to search.")
    results = _equity_candidates(q)
    # Fall back to treating the text as a symbol
    if not results and re.fullmatch(r"[A-Za-z0-9&\-]{1,20}", q):
        results.append({"ticker": q.upper() + ".NS", "name": q.upper(), "note": "direct symbol"})
    if not results:
        raise ScreenerError(f"No equity found for '{q}'. Try the NSE symbol (e.g. TCS).")
    return results


# ---- auto-suggest (names pop up while typing) ----
_SUGGEST_CACHE = {}


def _rank(q: str, name: str, ticker: str = "") -> int:
    """0 = symbol starts with text, 1 = name starts with text, 2 = a word starts with it, 3 = contains."""
    ql, n = q.lower(), name.lower()
    t = ticker.lower().replace(".ns", "").replace(".bo", "")
    if t.startswith(ql):
        return 0
    if n.startswith(ql):
        return 1
    if re.search(r"\b" + re.escape(ql), n):
        return 2
    return 3


def suggest_equities(query: str, limit: int = 10) -> list:
    """Best-matching stock names for the text typed so far (used by the pop-up list)."""
    q = query.strip()
    if len(q) < 2:
        return []
    key = ("eq", q.lower(), limit)
    if key not in _SUGGEST_CACHE:
        cands = _equity_candidates(q, yahoo_timeout=6)
        cands.sort(key=lambda m: (_rank(q, m["name"], m["ticker"]), m["ticker"].endswith(".BO"),
                                  m["name"].lower()))  # best match first, NSE before BSE
        _SUGGEST_CACHE[key] = cands[:limit]
    return _SUGGEST_CACHE[key]


def suggest_funds(query: str, limit: int = 12) -> list:
    """Best-matching mutual fund names for the text typed so far."""
    q = query.strip()
    if len(q) < 3:
        return []
    key = ("mf", q.lower(), limit)
    if key not in _SUGGEST_CACHE:
        try:
            funds = search_funds(q)
        except Exception:  # noqa: BLE001
            return []
        funds.sort(key=lambda f: (_rank(q, f["schemeName"]), not is_direct_growth(f["schemeName"]),
                                  f["schemeName"]))
        _SUGGEST_CACHE[key] = [{"code": f["schemeCode"], "name": f["schemeName"]} for f in funds[:limit]]
    return _SUGGEST_CACHE[key]


def match_label(m: dict) -> str:
    """Text shown for one search match / suggestion."""
    return f"{m['name']}   [{m['ticker']}]   {m['note']}" if "ticker" in m else m["name"]


def search_mutual_funds(query: str) -> list:
    """Find ALL mutual fund schemes matching the text -> [{'code','name'}] (Direct-Growth first)."""
    q = query.strip()
    if not q:
        raise ScreenerError("Type a fund name to search.")
    try:
        funds = search_funds(q)
    except Exception as e:  # noqa: BLE001
        raise ScreenerError(f"Could not reach the mutual fund data service: {e}")
    if not funds:
        raise ScreenerError(f"No mutual fund found for '{q}'.")
    funds = sorted(funds, key=lambda f: (not is_direct_growth(f["schemeName"]), f["schemeName"]))
    return [{"code": f["schemeCode"], "name": f["schemeName"]} for f in funds]


def load_equity_history(ticker: str, name: str = None) -> dict:
    """Full price history (max) of a stock/index for charting."""
    raw = yf.download(ticker, period="max", interval="1d", auto_adjust=True, progress=False)
    if raw is None or raw.empty:
        raise ScreenerError(f"No price data found for {ticker}.")
    close = _close_series(raw)
    if len(close) < 2:
        raise ScreenerError(f"Not enough price history for {ticker}.")
    return {"kind": "equity", "name": name or ticker, "id": ticker, "series": close}


def load_fund_history(code, name: str = None) -> dict:
    nav, meta = fetch_fund(code)
    if len(nav) < 2:
        raise ScreenerError("Not enough NAV history for this scheme.")
    return {"kind": "fund", "name": name or meta.get("scheme_name") or str(code), "id": code, "series": nav}


def analyze_equity(ticker: str, name: str = None) -> dict:
    """Full picture of one stock: returns, risk, dividends, news, chart data."""
    log(f"Downloading full price history for {ticker} ...")
    raw = yf.download(ticker, period="max", interval="1d", auto_adjust=True, progress=False)
    if raw is None or raw.empty:
        raise ScreenerError(f"No price data found for {ticker}.")
    close = _close_series(raw)
    if len(close) < 5:
        raise ScreenerError(f"Not enough price history for {ticker}.")

    row = {"Price": round(float(close.iloc[-1]), 2)}
    row.update(returns_row(close))
    row.update(risk_metrics(close))
    row.update(range_stats(close))

    log("Fetching dividend history ...")
    div = get_dividend_series(ticker)
    row.update(dividend_summary(div, row["Price"]))
    recent = []
    if div is not None and not div.empty:
        recent = [(d.strftime("%Y-%m-%d"), float(a)) for d, a in div.tail(6).items()]

    info = {}
    log("Fetching company details ...")
    try:
        raw_info = yf.Ticker(ticker).info or {}
        name = name or raw_info.get("longName") or ticker
        if raw_info.get("sector"):
            info["Sector"] = raw_info["sector"]
        if raw_info.get("industry"):
            info["Industry"] = raw_info["industry"]
        if raw_info.get("marketCap"):
            info["Market Cap"] = f"Rs {raw_info['marketCap'] / 1e7:,.0f} Cr"
        if raw_info.get("trailingPE"):
            info["P/E Ratio"] = f"{raw_info['trailingPE']:.1f}"
    except Exception:  # noqa: BLE001
        pass
    name = name or ticker

    log("Fetching latest news ...")
    items = news_items(name)
    row.update(sentiment_from_items(items))
    row["Red_Flags"] = red_flags(row)
    row["Score"] = signal_score(row)
    row["Signal"] = score_label(row["Score"])
    return {"kind": "equity", "name": name, "id": ticker, "series": close, "row": row,
            "news": items, "dividends": recent, "info": info}


def analyze_fund(code, name: str = None) -> dict:
    """Full picture of one mutual fund scheme (complete NAV history since launch)."""
    log(f"Downloading full NAV history (scheme {code}) ...")
    try:
        nav, meta = fetch_fund(code)
    except Exception as e:  # noqa: BLE001
        raise ScreenerError(f"Could not download NAV data: {e}")
    if len(nav) < 30:
        raise ScreenerError("Not enough NAV history for this scheme.")
    name = name or meta.get("scheme_name") or str(code)

    row = {"NAV": round(float(nav.iloc[-1]), 2), "NAV_Date": nav.index[-1].strftime("%d %b %Y"),
           "Inception_Date": nav.index[0].strftime("%d %b %Y")}
    row.update(returns_row(nav))
    row.update(risk_metrics(nav))
    row.update(range_stats(nav))
    years = (nav.index[-1] - nav.index[0]).days / 365.25
    total = (float(nav.iloc[-1]) / float(nav.iloc[0]) - 1) * 100
    row["Ret_inception_%"] = round(total, 2)
    row["CAGR_inception_%"] = round(((1 + total / 100) ** (1 / years) - 1) * 100, 2) if years >= 1 else np.nan

    log("Fetching latest news ...")
    items = news_items(fund_search_name(name), "mutual fund")
    row.update(sentiment_from_items(items))
    row["Red_Flags"] = red_flags(row)
    row["Score"] = signal_score(row)
    row["Signal"] = score_label(row["Score"])
    info = {"Fund House": meta.get("fund_house"), "Category": meta.get("scheme_category"),
            "Type": meta.get("scheme_type")}
    info = {k: v for k, v in info.items() if v}
    return {"kind": "fund", "name": name, "id": code, "series": nav, "row": row,
            "news": items, "dividends": None, "info": info}


def build_stats(res: dict) -> list:
    """Coloured stat tiles for the Search tab: [(label, text, bg, fg)]."""
    row, is_eq = res["row"], res["kind"] == "equity"
    tiles = []

    def tile(label, col, key=None):
        t, bg, fg = cell_style(col, row.get(key or col))
        tiles.append((label, t, bg, fg))

    def plain(label, text, bg="#ffffff", fg="#1b1b1b"):
        tiles.append((label, text, bg, fg))

    price = row.get("Price") if is_eq else row.get("NAV")
    plain("Price" if is_eq else "NAV", f"Rs {price:,.2f}" if _isnum(price) else "-")
    plain("52-week High", f"Rs {row['High_52w']:,.2f}")
    plain("52-week Low", f"Rs {row['Low_52w']:,.2f}")
    bg, fg = return_style(row.get("From_High_%"), 30)
    plain("From 52W High", f"{row['From_High_%']:.1f}%" if _isnum(row.get("From_High_%")) else "-", bg, fg)
    tile("Volatility 1Y", "Volatility_1y_%")
    tile("Max Drop 1Y", "MaxDrawdown_1y_%")
    if is_eq:
        tile("Dividend Yield", "Div_Yield_%")
        tile("Dividend Trend", "Div_Trend")
        plain("Last Dividend", row.get("Last_Div_Date") or "-")
    else:
        tile("3Y CAGR", "CAGR_3y_%")
        tile("5Y CAGR", "CAGR_5y_%")
        tile("Since launch CAGR", "CAGR_inception_%")
        rt = row.get("Ret_inception_%")
        rbg, rfg = return_style(rt, 300)
        plain("Total return since launch", f"{rt:+,.1f}%" if _isnum(rt) else "-", rbg, rfg)
        plain("Latest NAV date", row.get("NAV_Date", "-"))
        plain("Launch (first NAV)", row.get("Inception_Date", "-"))
    tile("News Mood", "News_Flag")
    tile("Red Flags", "Red_Flags")
    for k, v in res.get("info", {}).items():
        plain(k, str(v))
    return tiles


# --------------------------------------------------------------------------
# INTERACTIVE HTML CHART (opens in the browser, works offline)
# --------------------------------------------------------------------------
CHART_HTML = r"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>__TITLE__ - Chart</title>
<style>
:root{--bg:#f4f6f9;--card:#ffffff;--text:#1b2a3a;--muted:#607d8b;--grid:#e3e8ee;--up:#1f9d55;--down:#d93b3b;--navy:#1f3a5f}
body.dark{--bg:#0f1720;--card:#16212e;--text:#e6edf3;--muted:#8aa0b4;--grid:#243447;--up:#3ddc84;--down:#ff6b6b;--navy:#9fb7d6}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font-family:'Segoe UI',system-ui,Arial,sans-serif}
#top{display:flex;align-items:center;gap:18px;padding:14px 20px;background:var(--navy);color:#fff;flex-wrap:wrap}
body.dark #top{color:#0f1720}
h1{margin:0;font-size:22px}
#sub{opacity:.85;font-size:13px}
#pricebox{margin-left:auto;text-align:right}
#price{font-size:26px;font-weight:700}
#chg{font-size:15px;font-weight:600;margin-left:8px}
button{font:inherit;cursor:pointer}
#theme{border:0;border-radius:6px;padding:6px 12px;background:rgba(255,255,255,.22);color:inherit}
#bar{display:flex;gap:6px;padding:12px 20px 4px;flex-wrap:wrap}
#bar button{border:1px solid var(--grid);background:var(--card);color:var(--text);padding:6px 16px;border-radius:6px;font-weight:600}
#bar button.on{background:var(--navy);color:#fff;border-color:var(--navy)}
body.dark #bar button.on{color:#0f1720}
#bar button:disabled{opacity:.35;cursor:not-allowed}
#stats{padding:6px 20px 8px;font-size:14px;color:var(--muted)}
#stats b{color:var(--text)}
#wrap{margin:0 20px;height:calc(100vh - 235px);min-height:320px;background:var(--card);border:1px solid var(--grid);border-radius:10px}
canvas{width:100%;height:100%;display:block;cursor:crosshair}
#foot{padding:8px 20px;font-size:12px;color:var(--muted)}
</style></head><body>
<div id="top">
  <div><h1 id="title"></h1><div id="sub"></div></div>
  <div id="pricebox"><span id="price"></span><span id="chg"></span><div id="asof" style="font-size:12px;opacity:.85"></div></div>
  <button id="theme">Dark mode</button>
</div>
<div id="bar"></div>
<div id="stats"></div>
<div id="wrap"><canvas id="cv"></canvas></div>
<div id="foot"></div>
<script>
const D = __DATA__;
const $ = id => document.getElementById(id);
const cv = $('cv'), ctx = cv.getContext('2d');
const RANGES = [['1D',null],['5D',null],['1M',{m:1}],['6M',{m:6}],['1Y',{y:1}],['3Y',{y:3}],['5Y',{y:5}],['MAX',{}]];
let cur = D.daily.d.length > 260 ? '1Y' : 'MAX', hoverX = null;
const pad = n => String(n).padStart(2, '0');
const parse = s => new Date(s.length > 10 ? s.replace(' ', 'T') : s + 'T00:00:00');
const fmtP = v => '\u20B9' + v.toLocaleString('en-IN', {minimumFractionDigits: 2, maximumFractionDigits: 2});
const isIntra = r => r === '1D' || r === '5D';

function getSeries(r) {
  if (isIntra(r)) return D.intra[r] || null;
  const d = D.daily.d, v = D.daily.v, opt = RANGES.find(x => x[0] === r)[1];
  if (!opt || (!opt.m && !opt.y)) return D.daily;
  const cut = parse(d[d.length - 1]);
  if (opt.m) cut.setMonth(cut.getMonth() - opt.m);
  if (opt.y) cut.setFullYear(cut.getFullYear() - opt.y);
  const cs = cut.getFullYear() + '-' + pad(cut.getMonth() + 1) + '-' + pad(cut.getDate());
  let i = 0;
  while (i < d.length - 1 && d[i] < cs) i++;
  return {d: d.slice(i), v: v.slice(i)};
}
function colors() {
  const s = getComputedStyle(document.body), g = k => s.getPropertyValue(k).trim();
  return {up: g('--up'), down: g('--down'), grid: g('--grid'), muted: g('--muted'), text: g('--text'), card: g('--card')};
}
function xlabel(sd) {
  const dt = parse(sd);
  if (cur === '1D') return sd.slice(11, 16);
  if (cur === '5D') return dt.toLocaleDateString('en-GB', {day: '2-digit', month: 'short'}) + ' ' + sd.slice(11, 16);
  if (['1M', '6M', '1Y'].includes(cur)) return dt.toLocaleDateString('en-GB', {day: '2-digit', month: 'short'});
  return dt.toLocaleDateString('en-GB', {month: 'short', year: 'numeric'});
}
function draw() {
  document.querySelectorAll('#bar button').forEach(b => b.classList.toggle('on', b.textContent === cur));
  const s = getSeries(cur);
  const r = cv.getBoundingClientRect(), dpr = window.devicePixelRatio || 1;
  cv.width = Math.round(r.width * dpr); cv.height = Math.round(r.height * dpr);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  const W = r.width, H = r.height, C = colors();
  ctx.clearRect(0, 0, W, H);
  if (!s || s.v.length < 2) {
    ctx.fillStyle = C.muted; ctx.font = '15px Segoe UI, sans-serif'; ctx.textAlign = 'center';
    ctx.fillText('No data for this range', W / 2, H / 2); $('stats').textContent = ''; return;
  }
  const v = s.v, n = v.length, pl = 78, pr = 24, pt = 18, pb = 34;
  let lo = Math.min(...v), hi = Math.max(...v);
  const span = (hi - lo) || 1; lo -= span * 0.06; hi += span * 0.06;
  const sp = hi - lo;
  const X = i => pl + (W - pl - pr) * i / (n - 1), Y = p => pt + (H - pt - pb) * (1 - (p - lo) / sp);
  const up = v[n - 1] >= v[0], col = up ? C.up : C.down;
  ctx.font = '11px Segoe UI, sans-serif';
  for (let k = 0; k <= 5; k++) {
    const p = lo + sp * k / 5, y = Y(p);
    ctx.strokeStyle = C.grid; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pl, y); ctx.lineTo(W - pr, y); ctx.stroke();
    ctx.fillStyle = C.muted; ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
    ctx.fillText(p.toLocaleString('en-IN', {maximumFractionDigits: hi >= 100 ? 0 : 2}), pl - 8, y);
  }
  ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  for (let k = 0; k < 6; k++) {
    const i = Math.round((n - 1) * k / 5);
    ctx.fillText(xlabel(s.d[i]), Math.min(Math.max(X(i), pl + 24), W - pr - 24), H - pb + 9);
  }
  const g = ctx.createLinearGradient(0, pt, 0, H - pb);
  g.addColorStop(0, col + '55'); g.addColorStop(1, col + '05');
  ctx.beginPath(); ctx.moveTo(X(0), H - pb);
  for (let i = 0; i < n; i++) ctx.lineTo(X(i), Y(v[i]));
  ctx.lineTo(X(n - 1), H - pb); ctx.closePath(); ctx.fillStyle = g; ctx.fill();
  ctx.beginPath();
  for (let i = 0; i < n; i++) { if (i) ctx.lineTo(X(i), Y(v[i])); else ctx.moveTo(X(i), Y(v[i])); }
  ctx.strokeStyle = col; ctx.lineWidth = 2; ctx.lineJoin = 'round'; ctx.stroke();
  const vmax = Math.max(...v), vmin = Math.min(...v);
  [[v.indexOf(vmax), 'High', C.up, vmax], [v.indexOf(vmin), 'Low', C.down, vmin]].forEach(([i, t, c, val]) => {
    ctx.fillStyle = c; ctx.beginPath(); ctx.arc(X(i), Y(val), 4, 0, 7); ctx.fill();
    ctx.font = 'bold 11px Segoe UI, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'alphabetic';
    ctx.fillText(t + ' ' + fmtP(val), Math.min(Math.max(X(i), pl + 60), W - pr - 60), t === 'High' ? Y(val) - 9 : Y(val) + 18);
  });
  if (hoverX !== null) {
    let i = Math.round((hoverX - pl) / (W - pl - pr) * (n - 1)); i = Math.max(0, Math.min(n - 1, i));
    const x = X(i), y = Y(v[i]);
    ctx.setLineDash([5, 4]); ctx.strokeStyle = C.muted; ctx.lineWidth = 1; ctx.beginPath();
    ctx.moveTo(x, pt); ctx.lineTo(x, H - pb); ctx.moveTo(pl, y); ctx.lineTo(W - pr, y); ctx.stroke(); ctx.setLineDash([]);
    ctx.fillStyle = col; ctx.beginPath(); ctx.arc(x, y, 5.5, 0, 7); ctx.fill();
    ctx.strokeStyle = C.card; ctx.lineWidth = 2; ctx.stroke();
    const chg = (v[i] / v[0] - 1) * 100, dt = parse(s.d[i]);
    const l1 = isIntra(cur)
      ? dt.toLocaleString('en-GB', {weekday: 'short', day: '2-digit', month: 'short', year: 'numeric', hour: '2-digit', minute: '2-digit'})
      : dt.toLocaleDateString('en-GB', {weekday: 'short', day: '2-digit', month: 'short', year: 'numeric'});
    const l2 = 'Price  ' + fmtP(v[i]), l3 = 'Since start  ' + (chg >= 0 ? '+' : '') + chg.toFixed(2) + '%';
    ctx.font = 'bold 12px Segoe UI, sans-serif';
    const bw = Math.max(ctx.measureText(l1).width, ctx.measureText(l2).width, ctx.measureText(l3).width) + 26, bh = 74;
    let bx = x + 16; if (bx + bw > W - 4) bx = x - 16 - bw;
    const by = Math.max(pt, Math.min(y - bh / 2, H - pb - bh));
    ctx.fillStyle = '#1f3a5f'; ctx.fillRect(bx, by, bw, bh);
    ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
    ctx.fillStyle = '#b8c9de'; ctx.fillText(l1, bx + 13, by + 16);
    ctx.fillStyle = '#ffffff'; ctx.fillText(l2, bx + 13, by + 37);
    ctx.fillStyle = chg >= 0 ? '#7dffa8' : '#ff9a9a'; ctx.fillText(l3, bx + 13, by + 58);
  }
  const chgR = (v[n - 1] / v[0] - 1) * 100;
  $('stats').innerHTML = '<b style="color:' + col + '">' + cur + ': ' + (chgR >= 0 ? '\u25B2 +' : '\u25BC ') + chgR.toFixed(2) + '%</b>' +
    ' &nbsp;|&nbsp; High <b>' + fmtP(vmax) + '</b> &nbsp;|&nbsp; Low <b>' + fmtP(vmin) + '</b> &nbsp;|&nbsp; ' + n.toLocaleString() +
    ' points &nbsp;|&nbsp; ' + s.d[0].slice(0, 16) + ' \u2192 ' + s.d[n - 1].slice(0, 16) +
    ' &nbsp;|&nbsp; <i>move the mouse over the chart for date & price</i>';
}
(function init() {
  $('title').textContent = D.name;
  $('sub').textContent = D.id + '  \u00B7  ' + (D.kind === 'fund' ? 'Mutual fund NAV' : 'Equity');
  const dv = D.daily.v, dd = D.daily.d, last = dv[dv.length - 1], prev = dv.length > 1 ? dv[dv.length - 2] : last;
  $('price').textContent = fmtP(last);
  const ch = last - prev, cp = prev ? ch / prev * 100 : 0;
  $('chg').textContent = (ch >= 0 ? '\u25B2 +' : '\u25BC ') + ch.toFixed(2) + ' (' + cp.toFixed(2) + '%)';
  $('chg').style.color = ch >= 0 ? '#7dffa8' : '#ff9a9a';
  $('asof').textContent = (D.kind === 'fund' ? 'NAV of ' : 'Last close ') + dd[dd.length - 1];
  $('foot').textContent = 'Snapshot generated ' + D.generated + '. Data: Yahoo Finance / AMFI (mfapi.in). Educational use only - not investment advice.';
  RANGES.forEach(([r]) => {
    const b = document.createElement('button'); b.textContent = r;
    if (isIntra(r) && !D.intra[r]) { b.disabled = true; b.title = 'Intraday data not available (market closed, or this is a mutual fund)'; }
    b.onclick = () => { cur = r; draw(); };
    $('bar').appendChild(b);
  });
  if (matchMedia('(prefers-color-scheme: dark)').matches) document.body.classList.add('dark');
  $('theme').onclick = () => { document.body.classList.toggle('dark'); $('theme').textContent = document.body.classList.contains('dark') ? 'Light mode' : 'Dark mode'; draw(); };
  cv.addEventListener('mousemove', e => { hoverX = e.clientX - cv.getBoundingClientRect().left; draw(); });
  cv.addEventListener('mouseleave', () => { hoverX = null; draw(); });
  cv.addEventListener('touchmove', e => { hoverX = e.touches[0].clientX - cv.getBoundingClientRect().left; draw(); }, {passive: true});
  window.addEventListener('resize', draw);
  draw();
})();
</script></body></html>
"""


def build_chart_html(res: dict, intraday: dict = None) -> str:
    """Self-contained interactive chart page (hover shows date + price)."""
    s = res["series"].dropna()
    daily = {"d": [d.strftime("%Y-%m-%d") for d in s.index], "v": [round(float(v), 4) for v in s.values]}
    intra = {}
    for k, ser in (intraday or {}).items():
        if ser is not None and len(ser) > 1:
            intra[k] = {"d": [d.strftime("%Y-%m-%d %H:%M") for d in ser.index],
                        "v": [round(float(v), 4) for v in ser.values]}
    payload = {"name": str(res["name"]), "id": str(res["id"]), "kind": res["kind"], "daily": daily,
               "intra": intra, "generated": datetime.now().strftime("%d %b %Y %H:%M:%S")}
    data = json.dumps(payload).replace("</", "<\\/")
    return CHART_HTML.replace("__TITLE__", html.escape(str(res["name"]))).replace("__DATA__", data)


def write_chart_html(res: dict, intraday: dict = None) -> str:
    """Save the chart page to a temp file and return its path."""
    fd, path = tempfile.mkstemp(suffix=".html", prefix="chart_")
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        f.write(build_chart_html(res, intraday))
    return path


# --------------------------------------------------------------------------
# DISPLAY HELPERS (text summary) + COMMAND LINE
# --------------------------------------------------------------------------
STOCK_COLS = ["Symbol", "Company", "Category", "Signal", "Price", "Ret_1m_%", "Ret_2m_%",
              "Ret_6m_%", "Ret_1y_%", "Ret_5y_%", "Volatility_1y_%", "MaxDrawdown_1y_%",
              "Div_Yield_%", "Div_Trend", "News_Flag", "Red_Flags"]
FUND_COLS = ["Fund", "Signal", "NAV", "Ret_1m_%", "Ret_2m_%", "Ret_6m_%", "Ret_1y_%",
             "CAGR_3y_%", "CAGR_5y_%", "Volatility_1y_%", "MaxDrawdown_1y_%", "News_Flag",
             "Red_Flags"]


def summary_text(kind: str, period: str, df: pd.DataFrame, buckets: dict) -> str:
    unit = "stocks" if kind == "stocks" else "funds"
    name_col = "Symbol" if kind == "stocks" else "Fund"
    lines = [f"How many {unit} grew in the last {period.upper()} (whole universe):"]
    for th, names in buckets.items():
        preview = ", ".join(n[:28] for n in names[:6]) + (" ..." if len(names) > 6 else "")
        lines.append(f"  >= {th:>2}%  : {len(names):>3}   {preview}")

    if "Red_Flags" in df.columns:
        lines.append(f"\nRed flags among the selected {unit}:")
        flagged = df[df["Red_Flags"] != "-"]
        if flagged.empty:
            lines.append("  None.")
        for _, r in flagged.iterrows():
            lines.append(f"  {str(r[name_col])[:60]}: {r['Red_Flags']}")
    if "Negative_Headlines" in df.columns:
        lines.append("\nNegative headlines (last 30 days):")
        any_neg = False
        for _, r in df.iterrows():
            if r["Negative_Headlines"]:
                any_neg = True
                lines.append(f"  {str(r[name_col])[:60]}:")
                lines += [f"     - {h}" for h in r["Negative_Headlines"].split(" || ")]
        if not any_neg:
            lines.append("  None found.")
    if kind == "funds":
        lines.append("\nNote: Growth plans pay no dividend (profit stays in NAV). "
                     "IDCW plans pay out, but NAV falls by the same amount.")
    lines.append("\nEducational tool only - not investment advice.")
    return "\n".join(lines)


def cli_stocks(args):
    try:
        df, buckets = screen_stocks(args.universe, args.period, args.min_growth, args.top,
                                    args.consistent, not args.no_news, not args.no_dividends)
    except ScreenerError as e:
        sys.exit(str(e))
    pd.set_option("display.width", 250)
    pd.set_option("display.max_columns", 50)
    pd.set_option("display.max_colwidth", 30)
    print(f"\n=== TOP {len(df)} STOCKS by {args.period.upper()} return ===\n")
    print(df[[c for c in STOCK_COLS if c in df.columns]].to_string(index=False))
    print("\n" + summary_text("stocks", args.period, df, buckets))
    out = f"stock_screen_{args.universe}_{args.period}_{datetime.now():%Y%m%d}.csv"
    df.to_csv(out, index=False)
    print(f"\nSaved full results to {out}")


def cli_funds(args):
    try:
        df, buckets = screen_funds(args.query, args.period, args.min_growth, args.top,
                                   args.max_funds, args.all_plans, args.news)
    except ScreenerError as e:
        sys.exit(str(e))
    pd.set_option("display.width", 250)
    pd.set_option("display.max_columns", 50)
    pd.set_option("display.max_colwidth", 55)
    print(f"\n=== TOP {len(df)} FUNDS by {args.period.upper()} return ===\n")
    print(df[[c for c in FUND_COLS if c in df.columns]].to_string(index=False))
    print("\n" + summary_text("funds", args.period, df, buckets))
    out = f"fund_screen_{args.period}_{datetime.now():%Y%m%d}.csv"
    df.to_csv(out, index=False)
    print(f"Saved full results to {out}")


# --------------------------------------------------------------------------
# GUI - INTERACTIVE CHART (hover crosshair with date + price)
# --------------------------------------------------------------------------
class InteractiveChart:
    """Line/area chart on a Tk canvas. Hover shows a crosshair with date and price."""

    PAD = (68, 20, 18, 30)  # left, right, top, bottom

    def __init__(self, canvas):
        self.c = canvas
        self.s, self.intraday, self.message = None, False, "Nothing to show yet"
        self.pts, self.vals, self.dates = [], [], []
        self.w = self.h = 0
        self.color = "#1f9d55"
        canvas.bind("<Motion>", self._move)
        canvas.bind("<Leave>", lambda e: canvas.delete("hover"))
        canvas.bind("<Configure>", lambda e: self.redraw())

    def set_series(self, series, intraday=False, message=""):
        self.s = None if series is None else series.dropna()
        self.intraday = intraday
        self.message = message or "No price history available"
        self.redraw()

    def stats(self):
        if not self.vals:
            return None
        return {"chg": (self.vals[-1] / self.vals[0] - 1) * 100, "hi": max(self.vals),
                "lo": min(self.vals), "n": len(self.vals)}

    def redraw(self):
        c = self.c
        c.delete("all")
        self.pts, self.vals, self.dates = [], [], []
        w = self.w = max(int(c.winfo_width()), 300)
        h = self.h = max(int(c.winfo_height()), 160)
        s = self.s
        if s is None or len(s) < 2:
            c.create_text(w / 2, h / 2, text=self.message, fill="#78909c", font=("Segoe UI", 11))
            return
        if len(s) > 2000:
            s = s.iloc[np.linspace(0, len(s) - 1, 2000).astype(int)]
        pl, pr, pt, pb = self.PAD
        lo, hi = float(s.min()), float(s.max())
        span = (hi - lo) or 1.0
        lo, hi = lo - span * 0.06, hi + span * 0.06
        span = hi - lo
        n = len(s)
        X = lambda i: pl + (w - pl - pr) * i / (n - 1)  # noqa: E731
        Y = lambda v: pt + (h - pt - pb) * (1 - (v - lo) / span)  # noqa: E731

        vals = [float(v) for v in s.values]
        up = vals[-1] >= vals[0]
        line, fill = ("#1f9d55", "#dcf3e5") if up else ("#d93b3b", "#fbe1e1")
        self.color = line
        small = ("Segoe UI", 8)
        for k in range(5):
            v = lo + span * k / 4
            y = Y(v)
            c.create_line(pl, y, w - pr, y, fill="#e3e8ee")
            c.create_text(pl - 6, y, text=f"{v:,.0f}" if hi >= 100 else f"{v:,.2f}",
                          anchor="e", fill="#607d8b", font=small)
        pts = [(X(i), Y(v)) for i, v in enumerate(vals)]
        flat = [z for p in pts for z in p]
        c.create_polygon([pts[0][0], h - pb] + flat + [pts[-1][0], h - pb], fill=fill, outline="")
        c.create_line(*flat, fill=line, width=2)
        for i, colr, tag in ((int(np.argmax(vals)), "#1b7f3b", "High"),
                             (int(np.argmin(vals)), "#c62828", "Low")):
            x, y = pts[i]
            c.create_oval(x - 4, y - 4, x + 4, y + 4, fill=colr, outline="white")
            ty = min(max(y - 11 if tag == "High" else y + 12, 9), h - pb - 5)
            c.create_text(min(max(x, pl + 45), w - pr - 45), ty, text=f"{tag} {vals[i]:,.2f}",
                          fill=colr, font=("Segoe UI", 8, "bold"))
        c.create_oval(pts[-1][0] - 4, pts[-1][1] - 4, pts[-1][0] + 4, pts[-1][1] + 4,
                      fill=line, outline="white")
        fmt = "%d %b %H:%M" if self.intraday else "%d %b %Y"
        for k in range(5):
            i = round((n - 1) * k / 4)
            c.create_text(min(max(X(i), pl + 30), w - pr - 30), h - pb + 13,
                          text=s.index[i].strftime(fmt), fill="#607d8b", font=small)
        self.pts, self.vals, self.dates = pts, vals, list(s.index)

    def _move(self, e):
        if not self.pts:
            return
        pl, pr, pt, pb = self.PAD
        n = len(self.pts)
        frac = (e.x - pl) / max(self.w - pl - pr, 1)
        i = int(round(min(max(frac, 0.0), 1.0) * (n - 1)))
        x, y = self.pts[i]
        c = self.c
        c.delete("hover")
        c.create_line(x, pt, x, self.h - pb, fill="#90a4ae", dash=(4, 3), tags="hover")
        c.create_line(pl, y, self.w - pr, y, fill="#cfd8dc", dash=(2, 3), tags="hover")
        c.create_oval(x - 5, y - 5, x + 5, y + 5, fill=self.color, outline="white", width=2, tags="hover")
        v = self.vals[i]
        chg = (v / self.vals[0] - 1) * 100
        d = self.dates[i]
        when = d.strftime("%a %d %b %Y  %H:%M") if self.intraday else d.strftime("%a %d %b %Y")
        lines = [when, f"Price:  Rs {v:,.2f}", f"Since start:  {chg:+.2f}%"]
        bw = max(len(t) for t in lines) * 6.8 + 22
        bh = len(lines) * 18 + 12
        bx = x + 14 if x + 14 + bw < self.w - 4 else x - 14 - bw
        by = min(max(y - bh / 2, pt), self.h - pb - bh)
        c.create_rectangle(bx, by, bx + bw, by + bh, fill="#1f3a5f", outline="", tags="hover")
        cols = ("#b8c9de", "#ffffff", "#7dffa8" if chg >= 0 else "#ff9a9a")
        for k, (t, colr) in enumerate(zip(lines, cols)):
            c.create_text(bx + 11, by + 15 + k * 18, text=t, anchor="w", fill=colr,
                          font=("Segoe UI", 9, "bold" if k else "normal"), tags="hover")


# --------------------------------------------------------------------------
# GUI (Tkinter)
# --------------------------------------------------------------------------
UNIVERSE_LABELS = {
    "All (Nifty 50 + Midcap + Smallcap)": "all",
    "Nifty 50 (large cap)": "nifty50",
    "Nifty Midcap 150": "midcap",
    "Nifty Smallcap 250": "smallcap",
}
PERIOD_LABELS = {"1 Month": "1m", "2 Months": "2m", "6 Months": "6m",
                 "1 Year": "1y", "3 Years": "3y", "5 Years": "5y"}
FUND_PRESETS = ["small cap", "mid cap", "large cap", "flexi cap", "multi cap",
                "nifty 50 index", "elss", "focused", "value", "index"]
CHART_RANGES = ["1D", "5D", "1M", "6M", "1Y", "3Y", "5Y", "MAX"]
RANGE_OFFSETS = {"1M": pd.DateOffset(months=1), "6M": pd.DateOffset(months=6),
                 "1Y": pd.DateOffset(years=1), "3Y": pd.DateOffset(years=3),
                 "5Y": pd.DateOffset(years=5)}
NAVY, LIGHT = "#1f3a5f", "#f4f6f9"


def slice_range(s: pd.Series, r: str) -> pd.Series:
    if r == "MAX" or r not in RANGE_OFFSETS:
        return s
    return s[s.index >= s.index[-1] - RANGE_OFFSETS[r]]


def launch_gui():
    global LOGGER
    try:
        import tkinter as tk
        from tkinter import ttk, messagebox, filedialog, scrolledtext
    except ImportError:
        sys.exit("Tkinter is not installed. On Linux run:  sudo apt install python3-tk")
    import queue
    import threading
    import webbrowser

    try:  # sharper text on Windows high-DPI screens
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:  # noqa: BLE001
        pass

    q = queue.Queue()  # worker threads put callables here; the GUI thread runs them

    def bg(fn, cb):
        """Run fn() in a thread, then call cb(result, error) in the GUI thread."""
        def work():
            try:
                res = fn()
            except Exception as e:  # noqa: BLE001
                m = str(e) or e.__class__.__name__
                q.put(lambda m=m: cb(None, m))
                return
            q.put(lambda: cb(res, None))
        threading.Thread(target=work, daemon=True).start()

    def alive(widget) -> bool:
        try:
            return bool(widget.winfo_exists())
        except Exception:  # noqa: BLE001
            return False

    def parse_growth(text):
        t = text.strip().lower()
        if t in ("", "any", "none"):
            return True, None
        try:
            return True, float(t.replace("%", ""))
        except ValueError:
            messagebox.showerror("Invalid input", "Min growth must be a number like 10, 20, 50 or 'Any'.")
            return False, None

    def chip(parent, text, bg, fg, bold=False, size=9):
        return tk.Label(parent, text=text, bg=bg, fg=fg, padx=8, pady=3,
                        font=("Segoe UI", size, "bold" if bold else "normal"))

    # ------------------------------------------------------------------
    class ChartPanel(ttk.Frame):
        """Range buttons + interactive hover chart + Pop-out / Browser / Chart-tab buttons."""

        def __init__(self, master, app, buttons=("popout", "browser"), compact=False, initial="1Y"):
            super().__init__(master)
            self.app, self.res = app, None
            self.cache, self.loading = {}, set()
            self.range = tk.StringVar(value=initial)
            bar = tk.Frame(self, bg=LIGHT)
            bar.pack(fill="x")
            tk.Label(bar, text="Range:", bg=LIGHT, fg="#455a64", font=("Segoe UI", 9, "bold")).pack(side="left")
            for r in CHART_RANGES:
                ttk.Radiobutton(bar, text=r, value=r, variable=self.range, command=self.draw).pack(
                    side="left", padx=3)
            if "tab" in buttons:
                ttk.Button(bar, text="Chart tab (big)", command=app.show_chart_tab).pack(side="right", padx=2)
            if "browser" in buttons:
                ttk.Button(bar, text="Open in browser (HTML)", command=self.to_browser).pack(side="right", padx=2)
            if "popout" in buttons:
                ttk.Button(bar, text="Pop-out window", command=self.to_popout).pack(side="right", padx=2)
            self.info = tk.Label(self, text="", bg=LIGHT, fg="#455a64", anchor="w",
                                 font=("Segoe UI", 9, "bold"))
            self.info.pack(fill="x", pady=(2, 0))
            self.canvas = tk.Canvas(self, bg="white", highlightthickness=1,
                                    highlightbackground="#d0d7de", height=230 if compact else 480,
                                    cursor="crosshair")
            if compact:
                self.canvas.pack(fill="x")
            else:
                self.canvas.pack(fill="both", expand=True)
            self.chart = InteractiveChart(self.canvas)
            self.after(60000, self._auto)
            self.draw()

        def set_result(self, res):
            self.res, self.cache, self.loading = res, {}, set()
            self.draw()

        def draw(self):
            res, r = self.res, self.range.get()
            if res is None:
                self.chart.set_series(None, message="Search a stock or mutual fund - its chart appears here")
                self.info.config(text="")
                return
            if r in ("1D", "5D"):
                if res["kind"] != "equity":
                    self.chart.set_series(None, message="Intraday chart is for stocks only "
                                                        "(a mutual fund NAV is declared once a day)")
                    self.info.config(text="")
                    return
                ser = self.cache.get(r)
                if ser is None:
                    self.load_intraday(r)
                    self.chart.set_series(None, message="Loading intraday prices ...")
                    self.info.config(text="")
                    return
                if ser is False:
                    self.chart.set_series(None, message="Intraday data not available right now "
                                                        "(market closed or no data)")
                    self.info.config(text="")
                    return
                s = ser
            else:
                s = slice_range(res["series"], r)
            self.chart.set_series(s, intraday=r in ("1D", "5D"))
            st = self.chart.stats()
            if st:
                up = st["chg"] >= 0
                self.info.config(
                    fg="#1b7f3b" if up else "#c62828",
                    text=f"{r}:  {'▲' if up else '▼'} {st['chg']:+.2f}%     High Rs {st['hi']:,.2f}     "
                         f"Low Rs {st['lo']:,.2f}     {st['n']:,} points     |     "
                         f"move the mouse over the chart to see date & price")

        def load_intraday(self, r):
            res = self.res
            if res is None or r in self.loading:
                return
            self.loading.add(r)

            def done(ser, err):
                self.loading.discard(r)
                if self.res is not res or not alive(self):
                    return
                self.cache[r] = ser if ser is not None else False
                self.draw()

            bg(lambda: fetch_intraday(res["id"], r), done)

        def _auto(self):  # live refresh of the 1-day chart while the market is open
            try:
                if not alive(self):
                    return
                if self.res and self.res["kind"] == "equity" and self.range.get() == "1D" \
                        and is_market_open():
                    self.load_intraday("1D")
                self.after(60000, self._auto)
            except Exception:  # noqa: BLE001
                pass

        def to_popout(self):
            if self.res is not None:
                self.app.open_popup(self.res, self.range.get())

        def to_browser(self):
            if self.res is not None:
                self.app.open_browser(self.res)

    # ------------------------------------------------------------------
    class HeatTable(ttk.Frame):
        """Scrollable colour-coded table (per-cell colours, click header to sort)."""

        def __init__(self, master, on_click=None):
            super().__init__(master)
            self.on_click = on_click
            self.canvas = tk.Canvas(self, highlightthickness=0, background="#ffffff")
            vs = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
            hs = ttk.Scrollbar(self, orient="horizontal", command=self.canvas.xview)
            self.canvas.configure(yscrollcommand=vs.set, xscrollcommand=hs.set)
            self.canvas.grid(row=0, column=0, sticky="nsew")
            vs.grid(row=0, column=1, sticky="ns")
            hs.grid(row=1, column=0, sticky="ew")
            self.rowconfigure(0, weight=1)
            self.columnconfigure(0, weight=1)
            self.inner = tk.Frame(self.canvas, background="#ffffff")
            self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
            self.inner.bind("<Configure>",
                            lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
            self.canvas.bind("<Enter>", self._bind_wheel)
            self.canvas.bind("<Leave>", self._unbind_wheel)
            self.df, self.cols = None, []
            self.sort_col, self.sort_rev = None, True

        def _bind_wheel(self, _e):
            for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                self.canvas.bind_all(seq, self._wheel)

        def _unbind_wheel(self, _e):
            for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                self.canvas.unbind_all(seq)

        def _wheel(self, e):
            if getattr(e, "num", 0) == 4:
                d = -1
            elif getattr(e, "num", 0) == 5:
                d = 1
            else:
                d = -1 if e.delta > 0 else 1
            self.canvas.yview_scroll(d, "units")

        def set_data(self, df, cols):
            self.df, self.cols = df.reset_index(drop=True), cols
            self.sort_col, self.sort_rev = None, True
            self.render()

        def clear(self):
            self.df, self.cols = None, []
            for w in self.inner.winfo_children():
                w.destroy()

        def sort_by(self, col):
            if self.df is None:
                return
            if self.sort_col == col:
                self.sort_rev = not self.sort_rev
            else:
                self.sort_col, self.sort_rev = col, col not in LEFT_COLS
            key = "Score" if col == "Signal" and "Score" in self.df.columns else col
            kfun = (lambda s: s.astype(str).str.lower()) if col in LEFT_COLS else None
            self.df = self.df.sort_values(key, ascending=not self.sort_rev, key=kfun,
                                          na_position="last").reset_index(drop=True)
            self.render()

        def render(self):
            for w in self.inner.winfo_children():
                w.destroy()
            if self.df is None:
                return
            for j, c in enumerate(self.cols):
                arrow = (" ▼" if self.sort_rev else " ▲") if self.sort_col == c else ""
                h = tk.Label(self.inner, text=pretty(c) + arrow, bg=NAVY, fg="white",
                             font=("Segoe UI", 9, "bold"), padx=6, pady=7, cursor="hand2",
                             width=COLW.get(c, 11), anchor="w" if c in LEFT_COLS else "center")
                h.grid(row=0, column=j, sticky="nsew", padx=(0, 1), pady=(0, 1))
                h.bind("<Button-1>", lambda e, c=c: self.sort_by(c))
            for i, (_, r) in enumerate(self.df.iterrows(), start=1):
                for j, c in enumerate(self.cols):
                    txt, bg, fg = cell_style(c, r[c])
                    if c in ("Company", "Fund") and len(txt) > COLW[c]:
                        txt = txt[:COLW[c] - 1] + "…"
                    lab = tk.Label(self.inner, text=txt, bg=bg, fg=fg, padx=6, pady=5,
                                   font=("Segoe UI", 9, "bold" if j == 0 or c == "Signal" else "normal"),
                                   width=COLW.get(c, 11), anchor="w" if c in LEFT_COLS else "center")
                    if j == 0 and self.on_click:  # click a name -> pop-out chart
                        lab.config(cursor="hand2", fg="#0b57d0")
                        lab.bind("<Button-1>", lambda e, r=r: self.on_click(r))
                    lab.grid(row=i, column=j, sticky="nsew", padx=(0, 1), pady=(0, 1))

    # ------------------------------------------------------------------
    class ResultsView(ttk.Frame):
        """Chips + heat-map table + colour legend + coloured summary + Save button."""

        def __init__(self, master, app):
            super().__init__(master)
            self.app, self.df, self.kind = app, None, "stocks"
            self.chips = tk.Frame(self, bg=LIGHT)
            self.chips.pack(fill="x", pady=(0, 6))
            self.table = HeatTable(self, self.row_clicked)
            self.table.pack(fill="both", expand=True)

            leg = tk.Frame(self, bg=LIGHT)
            leg.pack(fill="x", pady=4)
            tk.Label(leg, text="Colour guide:", bg=LIGHT, fg="#455a64",
                     font=("Segoe UI", 9, "bold")).pack(side="left")
            for t, bg, fg in (("▲ big gain", "#1f9d55", "#fff"), ("▲ small gain", "#a7dcb8", "#1b1b1b"),
                              ("▼ small loss", "#f3b8b8", "#1b1b1b"), ("▼ big loss", "#d93b3b", "#fff")):
                chip(leg, t, bg, fg).pack(side="left", padx=2)
            tk.Label(leg, text="   Signal:", bg=LIGHT, fg="#455a64",
                     font=("Segoe UI", 9, "bold")).pack(side="left")
            for name, (bg, fg) in BADGES["Signal"].items():
                chip(leg, name, bg, fg, bold=True).pack(side="left", padx=2)
            tk.Label(leg, text="   Blue name = click to open its chart", bg=LIGHT, fg="#0b57d0",
                     font=("Segoe UI", 9)).pack(side="left")
            self.save_btn = ttk.Button(leg, text="Save results as CSV", command=self.save_csv,
                                       state="disabled")
            self.save_btn.pack(side="right")

            self.summary = scrolledtext.ScrolledText(self, height=9, wrap="word",
                                                     font=("Consolas", 10), bg="#fbfcfe")
            self.summary.pack(fill="x", pady=(2, 0))
            self.summary.tag_configure("head", font=("Segoe UI", 10, "bold"), foreground=NAVY)
            self.summary.tag_configure("sub", font=("Segoe UI", 9, "bold"), foreground="#37474f")
            self.summary.tag_configure("neg", foreground="#c62828")
            self.summary.tag_configure("pos", foreground="#2e7d32")
            self.summary.tag_configure("warn", foreground="#b26a00")
            self.summary.tag_configure("muted", foreground="#78909c")

        def row_clicked(self, row):
            if "Symbol" in row.index:
                company = row.get("Company")
                self.app.popup_chart_equity(f"{row['Symbol']}.NS",
                                            company if isinstance(company, str) else row["Symbol"])
            elif "Code" in row.index:
                self.app.popup_chart_fund(row["Code"], row["Fund"])

        def clear(self):
            self.table.clear()
            for w in self.chips.winfo_children():
                w.destroy()
            self.summary.delete("1.0", "end")
            self.save_btn.config(state="disabled")

        def append_log(self, msg):
            self.summary.insert("end", msg + "\n", "muted")
            self.summary.see("end")

        def show(self, kind, period, df, buckets):
            self.df, self.kind = df, kind
            unit = "stocks" if kind == "stocks" else "funds"
            for w in self.chips.winfo_children():
                w.destroy()
            tk.Label(self.chips, text=f"Grew in last {period.upper()} (all {unit} scanned):",
                     bg=LIGHT, fg="#455a64", font=("Segoe UI", 10, "bold")).pack(side="left")
            for th, (bg, fg) in ((10, ("#c8efd4", "#14532d")), (20, ("#6cc48a", "#0b3d1e")),
                                 (50, ("#1b7f3b", "#ffffff"))):
                chip(self.chips, f"≥ {th}%   {len(buckets[th])} {unit}", bg, fg, True, 10).pack(
                    side="left", padx=4)
            cols = [c for c in (STOCK_COLS if kind == "stocks" else FUND_COLS) if c in df.columns]
            self.table.set_data(df, cols)
            self.show_summary(summary_text(kind, period, df, buckets))
            self.save_btn.config(state="normal")

        def show_summary(self, text):
            self.summary.delete("1.0", "end")
            section = ""
            for line in text.split("\n"):
                tag = None
                if line.startswith("     - "):
                    tag = "neg"
                elif line and not line.startswith(" ") and line.endswith(":"):
                    tag = "head"
                    section = ("buckets" if line.startswith("How many") else
                               "flags" if line.startswith("Red flags") else "news")
                elif line.startswith("  ") and line.strip().endswith(":"):
                    tag = "sub"
                elif line.startswith("Educational") or line.startswith("Note:"):
                    tag = "muted"
                elif section == "buckets" and line.strip():
                    tag = "pos"
                elif section == "flags" and line.strip() and "None" not in line:
                    tag = "warn"
                if tag:
                    self.summary.insert("end", line + "\n", tag)
                else:
                    self.summary.insert("end", line + "\n")

        def save_csv(self):
            if self.df is None:
                return
            path = filedialog.asksaveasfilename(
                defaultextension=".csv", filetypes=[("CSV file", "*.csv")],
                initialfile=f"{self.kind}_screen_{datetime.now():%Y%m%d}.csv")
            if path:
                self.df.to_csv(path, index=False)
                messagebox.showinfo("Saved", f"Saved to:\n{path}")

    # ------------------------------------------------------------------
    class StockTab(ttk.Frame):
        def __init__(self, app):
            super().__init__(app.nb, padding=8)
            self.app = app
            box = ttk.LabelFrame(self, text=" Screen settings ", padding=8)
            box.pack(fill="x")
            self.universe = tk.StringVar(value=list(UNIVERSE_LABELS)[0])
            self.period = tk.StringVar(value="6 Months")
            self.growth = tk.StringVar(value="20")
            self.top = tk.IntVar(value=10)
            self.cons = tk.BooleanVar(value=False)
            self.news = tk.BooleanVar(value=True)
            self.div = tk.BooleanVar(value=True)

            ttk.Label(box, text="Market group:").grid(row=0, column=0, sticky="w")
            ttk.Combobox(box, textvariable=self.universe, values=list(UNIVERSE_LABELS),
                         state="readonly", width=34).grid(row=1, column=0, padx=(0, 14), sticky="w")
            ttk.Label(box, text="Rank by period:").grid(row=0, column=1, sticky="w")
            ttk.Combobox(box, textvariable=self.period, values=list(PERIOD_LABELS),
                         state="readonly", width=12).grid(row=1, column=1, padx=(0, 14), sticky="w")
            ttk.Label(box, text="Min growth % (Any/10/20/50):").grid(row=0, column=2, sticky="w")
            ttk.Combobox(box, textvariable=self.growth, values=["Any", "10", "20", "50", "100"],
                         width=10).grid(row=1, column=2, padx=(0, 14), sticky="w")
            ttk.Label(box, text="How many shares:").grid(row=0, column=3, sticky="w")
            ttk.Spinbox(box, from_=1, to=50, textvariable=self.top, width=6).grid(
                row=1, column=3, padx=(0, 14), sticky="w")
            ttk.Checkbutton(box, text="Positive in 1M, 2M & 6M (consistent)",
                            variable=self.cons).grid(row=2, column=0, sticky="w", pady=(8, 0))
            ttk.Checkbutton(box, text="Check news (negative flag)", variable=self.news).grid(
                row=2, column=1, columnspan=2, sticky="w", pady=(8, 0))
            ttk.Checkbutton(box, text="Check dividends", variable=self.div).grid(
                row=2, column=3, sticky="w", pady=(8, 0))
            self.btn = ttk.Button(box, text="Run Stock Screener", style="Accent.TButton",
                                  command=self.run)
            self.btn.grid(row=0, column=4, rowspan=3, padx=20, sticky="ns")

            self.results = ResultsView(self, app)
            self.results.pack(fill="both", expand=True, pady=(8, 0))

        def set_busy(self, busy):
            self.btn.config(state="disabled" if busy else "normal")

        def run(self):
            ok, growth = parse_growth(self.growth.get())
            if not ok:
                return
            p = dict(universe=UNIVERSE_LABELS[self.universe.get()],
                     period=PERIOD_LABELS[self.period.get()], min_growth=growth,
                     top=int(self.top.get()), consistent=self.cons.get(),
                     news=self.news.get(), dividends=self.div.get())
            self.results.clear()
            self.app.run_job(lambda: screen_stocks(**p),
                             lambda res: self.results.show("stocks", p["period"], *res),
                             self.results.append_log,
                             "Screening stocks ... (1-3 minutes for the full universe)")

    # ------------------------------------------------------------------
    class FundTab(ttk.Frame):
        def __init__(self, app):
            super().__init__(app.nb, padding=8)
            self.app = app
            box = ttk.LabelFrame(self, text=" Screen settings ", padding=8)
            box.pack(fill="x")
            self.query = tk.StringVar(value="small cap")
            self.period = tk.StringVar(value="1 Year")
            self.growth = tk.StringVar(value="Any")
            self.top = tk.IntVar(value=10)
            self.scan = tk.StringVar(value="100")
            self.all = tk.BooleanVar(value=False)
            self.news = tk.BooleanVar(value=False)

            ttk.Label(box, text="Fund type / name:").grid(row=0, column=0, sticky="w")
            ttk.Combobox(box, textvariable=self.query, values=FUND_PRESETS, width=26).grid(
                row=1, column=0, padx=(0, 14), sticky="w")
            ttk.Label(box, text="Rank by period:").grid(row=0, column=1, sticky="w")
            ttk.Combobox(box, textvariable=self.period, values=list(PERIOD_LABELS),
                         state="readonly", width=12).grid(row=1, column=1, padx=(0, 14), sticky="w")
            ttk.Label(box, text="Min growth % (Any/10/20/50):").grid(row=0, column=2, sticky="w")
            ttk.Combobox(box, textvariable=self.growth, values=["Any", "10", "20", "50", "100"],
                         width=10).grid(row=1, column=2, padx=(0, 14), sticky="w")
            ttk.Label(box, text="How many funds:").grid(row=0, column=3, sticky="w")
            ttk.Spinbox(box, from_=1, to=100, textvariable=self.top, width=6).grid(
                row=1, column=3, padx=(0, 14), sticky="w")
            ttk.Label(box, text="Schemes to scan (All = no limit):").grid(row=0, column=4, sticky="w")
            ttk.Combobox(box, textvariable=self.scan, values=["30", "100", "250", "500", "1000", "All"],
                         width=9).grid(row=1, column=4, padx=(0, 14), sticky="w")
            ttk.Checkbutton(box, text="Include Regular / IDCW plans too", variable=self.all).grid(
                row=2, column=0, sticky="w", pady=(8, 0))
            ttk.Checkbutton(box, text="Check news for top funds", variable=self.news).grid(
                row=2, column=1, columnspan=2, sticky="w", pady=(8, 0))
            self.btn = ttk.Button(box, text="Run Fund Screener", style="Accent.TButton",
                                  command=self.run)
            self.btn.grid(row=0, column=5, rowspan=3, padx=20, sticky="ns")

            self.results = ResultsView(self, app)
            self.results.pack(fill="both", expand=True, pady=(8, 0))

        def set_busy(self, busy):
            self.btn.config(state="disabled" if busy else "normal")

        def run(self):
            ok, growth = parse_growth(self.growth.get())
            if not ok:
                return
            query = self.query.get().strip()
            if not query:
                messagebox.showerror("Invalid input", "Please type a fund type or name.")
                return
            scan_txt = self.scan.get().strip().lower()
            try:
                scan = 0 if scan_txt in ("all", "0", "") else int(scan_txt)
            except ValueError:
                messagebox.showerror("Invalid input", "Schemes to scan must be a number or 'All'.")
                return
            p = dict(query=query, period=PERIOD_LABELS[self.period.get()], min_growth=growth,
                     top=int(self.top.get()), max_funds=scan,
                     all_plans=self.all.get(), news=self.news.get())
            self.results.clear()
            self.app.run_job(lambda: screen_funds(**p),
                             lambda res: self.results.show("funds", p["period"], *res),
                             self.results.append_log, "Screening mutual funds ...")

    # ------------------------------------------------------------------
    class SearchView(ttk.Frame):
        """Search ANY equity / mutual fund (unlimited list) + colourful detail page + live price."""

        def __init__(self, app):
            super().__init__(app.nb, padding=8)
            self.app = app
            self.kind = tk.StringVar(value="equity")
            self.query = tk.StringVar()
            self.filter = tk.StringVar()
            self.matches, self.shown, self.current = [], [], None
            self._live_id = None

            top = ttk.LabelFrame(self, text=" Search ", padding=8)
            top.pack(fill="x")
            # name pop-up (auto-suggest) state
            self.sugg_items, self.sugg_idx = [], -1
            self.sugg_win = self.sugg_lb = None
            self._sugg_after, self._sugg_gen, self._focus = None, 0, False

            ttk.Radiobutton(top, text="Equity (Stock)", value="equity", variable=self.kind,
                            command=self.hide_suggestions).pack(side="left")
            ttk.Radiobutton(top, text="Mutual Fund", value="fund", variable=self.kind,
                            command=self.hide_suggestions).pack(side="left", padx=(10, 18))
            entry = ttk.Entry(top, textvariable=self.query, width=42)
            entry.pack(side="left")
            self.entry = entry
            entry.bind("<KeyRelease>", self.on_type)
            entry.bind("<Down>", lambda e: self.sugg_move(1))
            entry.bind("<Up>", lambda e: self.sugg_move(-1))
            entry.bind("<Return>", self.on_enter)
            entry.bind("<Escape>", lambda e: self.hide_suggestions())
            entry.bind("<FocusIn>", lambda e: setattr(self, "_focus", True))
            entry.bind("<FocusOut>", self._focus_out)
            self.bind("<Unmap>", lambda e: self.hide_suggestions())
            self.btn = ttk.Button(top, text="Search", style="Accent.TButton", command=self.do_search)
            self.btn.pack(side="left", padx=8)
            ttk.Label(top, foreground="#607d8b",
                      text="Start typing - matching names pop up.  e.g. Reliance, TCS  |  Parag Parikh, SBI, Nippon"
                      ).pack(side="left", padx=8)

            body = ttk.Frame(self)
            body.pack(fill="both", expand=True, pady=8)
            left = ttk.Frame(body)
            left.pack(side="left", fill="y")
            self.count = ttk.Label(left, text="Matches - double-click one to analyse:",
                                   font=("Segoe UI", 9, "bold"))
            self.count.pack(anchor="w")
            frow = ttk.Frame(left)
            frow.pack(fill="x", pady=(2, 3))
            ttk.Label(frow, text="Filter list:").pack(side="left")
            fe = ttk.Entry(frow, textvariable=self.filter, width=30)
            fe.pack(side="left", padx=4)
            fe.bind("<KeyRelease>", lambda e: self.refill())
            lf = ttk.Frame(left)
            lf.pack(fill="y", expand=True)
            self.lb = tk.Listbox(lf, width=52, activestyle="none", exportselection=False,
                                 font=("Segoe UI", 9), selectbackground="#1f9d55",
                                 selectforeground="white")
            sb = ttk.Scrollbar(lf, command=self.lb.yview)
            self.lb.configure(yscrollcommand=sb.set)
            self.lb.pack(side="left", fill="y", expand=True)
            sb.pack(side="left", fill="y")
            self.lb.bind("<Double-Button-1>", lambda e: self.analyse())
            ttk.Button(left, text="Analyse selected", command=self.analyse).pack(fill="x", pady=(6, 0))

            right = ttk.Frame(body)
            right.pack(side="left", fill="both", expand=True, padx=(12, 0))
            head = tk.Frame(right, bg=LIGHT)
            head.pack(fill="x")
            self.title = tk.Label(head, text="Search a stock or mutual fund on the left",
                                  bg=LIGHT, fg=NAVY, font=("Segoe UI", 15, "bold"), anchor="w")
            self.title.pack(side="left")
            self.badge = tk.Label(head, text="", font=("Segoe UI", 11, "bold"), padx=8)
            self.badge.pack(side="left", padx=10)
            self.csv_btn = ttk.Button(head, text="Save history CSV", command=self.save_history)
            self.csv_btn.pack(side="right", padx=2)
            self.watch_btn = ttk.Button(head, text="Add to Watchlist", command=self.add_watch)
            self.watch_btn.pack(side="right", padx=2)

            pr = tk.Frame(right, bg=LIGHT)
            pr.pack(fill="x")
            self.price = tk.Label(pr, text="", bg=LIGHT, font=("Segoe UI", 20, "bold"))
            self.price.pack(side="left")
            self.day = tk.Label(pr, text="", font=("Segoe UI", 11, "bold"), padx=8)
            self.day.pack(side="left", padx=8)
            self.live = tk.Label(pr, text="", font=("Segoe UI", 9, "bold"), padx=8, pady=2)
            self.live.pack(side="left")
            self.upd = tk.Label(pr, text="", bg=LIGHT, fg="#78909c", font=("Segoe UI", 8))
            self.upd.pack(side="left", padx=8)
            self.subtitle = tk.Label(right, text="", bg=LIGHT, fg="#607d8b", anchor="w")
            self.subtitle.pack(fill="x")

            self.cards = tk.Frame(right, bg=LIGHT)
            self.cards.pack(fill="x", pady=6)

            self.panel = ChartPanel(right, app, buttons=("popout", "browser", "tab"), compact=True)
            self.panel.pack(fill="x")

            self.stats = tk.Frame(right, bg=LIGHT)
            self.stats.pack(fill="x", pady=(4, 0))

            self.details = scrolledtext.ScrolledText(right, height=6, wrap="word",
                                                     font=("Segoe UI", 10), bg="#fbfcfe")
            self.details.pack(fill="both", expand=True, pady=(6, 0))
            self.details.tag_configure("head", font=("Segoe UI", 10, "bold"), foreground=NAVY)
            self.details.tag_configure("neg", foreground="#c62828")
            self.details.tag_configure("pos", foreground="#2e7d32")
            self.details.tag_configure("muted", foreground="#78909c")

        def set_busy(self, busy):
            self.btn.config(state="disabled" if busy else "normal")

        # ----- name pop-up (auto-suggest while typing) -----
        def _focus_out(self, _e=None):
            self._focus = False
            self.after(250, self.hide_suggestions)

        def on_type(self, e):
            if getattr(e, "keysym", "") in ("Return", "Up", "Down", "Left", "Right", "Escape", "Tab",
                                            "Shift_L", "Shift_R", "Control_L", "Control_R",
                                            "Alt_L", "Alt_R", "Home", "End"):
                return
            if self._sugg_after is not None:
                try:
                    self.after_cancel(self._sugg_after)
                except Exception:  # noqa: BLE001
                    pass
                self._sugg_after = None
            need = 2 if self.kind.get() == "equity" else 3
            if len(self.query.get().strip()) < need:
                self.hide_suggestions()
                return
            self._sugg_after = self.after(350, self.fetch_suggestions)  # wait until typing pauses

        def fetch_suggestions(self):
            self._sugg_after = None
            text, kind = self.query.get().strip(), self.kind.get()
            if len(text) < (2 if kind == "equity" else 3):
                return
            self._sugg_gen += 1
            gen = self._sugg_gen
            fn = (lambda: suggest_equities(text)) if kind == "equity" else (lambda: suggest_funds(text))

            def done(items, err):
                if gen != self._sugg_gen or not alive(self):
                    return  # a newer keystroke / action made this result stale
                if not items or not self._focus or self.query.get().strip() != text \
                        or self.kind.get() != kind:
                    self.hide_suggestions()
                    return
                self.show_suggestions(items)

            bg(fn, done)

        def show_suggestions(self, items):
            self.sugg_items, self.sugg_idx = items, -1
            if self.sugg_win is None:
                win = tk.Toplevel(self)
                win.overrideredirect(True)
                try:
                    win.attributes("-topmost", True)
                except Exception:  # noqa: BLE001
                    pass
                frame = tk.Frame(win, bg=NAVY, padx=1, pady=1)
                frame.pack(fill="both", expand=True)
                lb = tk.Listbox(frame, activestyle="none", exportselection=False, borderwidth=0,
                                highlightthickness=0, background="white", font=("Segoe UI", 10),
                                selectbackground="#1f9d55", selectforeground="white", width=70)
                lb.pack(fill="both", expand=True)
                tk.Label(frame, text="  ↑ ↓ move   •   Enter / click = open   •   Esc = close",
                         bg="#eef3f8", fg="#607d8b", font=("Segoe UI", 8), anchor="w").pack(fill="x")
                lb.bind("<ButtonPress-1>", self.on_sugg_click)
                lb.bind("<Motion>", self.on_sugg_hover)
                self.sugg_win, self.sugg_lb = win, lb
            self.sugg_lb.delete(0, "end")
            for it in items:
                self.sugg_lb.insert("end", "  " + match_label(it))
            self.sugg_lb.config(height=min(len(items), 10))
            self.entry.update_idletasks()
            x = self.entry.winfo_rootx()
            y = self.entry.winfo_rooty() + self.entry.winfo_height() + 2
            self.sugg_win.geometry(f"+{x}+{y}")
            self.sugg_win.deiconify()
            self.sugg_win.lift()

        def hide_suggestions(self):
            self._sugg_gen += 1  # cancel any lookup still in flight
            if self._sugg_after is not None:
                try:
                    self.after_cancel(self._sugg_after)
                except Exception:  # noqa: BLE001
                    pass
                self._sugg_after = None
            self.sugg_items, self.sugg_idx = [], -1
            if self.sugg_win is not None:
                try:
                    self.sugg_win.withdraw()
                except Exception:  # noqa: BLE001
                    pass

        def _highlight(self, i):
            self.sugg_idx = i
            self.sugg_lb.selection_clear(0, "end")
            if i >= 0:
                self.sugg_lb.selection_set(i)
                self.sugg_lb.see(i)

        def sugg_move(self, d):
            if not self.sugg_items or self.sugg_win is None:
                return None
            self._highlight(max(-1, min(len(self.sugg_items) - 1, self.sugg_idx + d)))
            return "break"

        def on_sugg_hover(self, e):
            if self.sugg_items:
                self._highlight(self.sugg_lb.nearest(e.y))

        def on_sugg_click(self, e):
            self.choose_suggestion(self.sugg_lb.nearest(e.y))
            return "break"

        def on_enter(self, _e=None):
            if self.sugg_items and self.sugg_idx >= 0:
                self.choose_suggestion(self.sugg_idx)
            else:
                self.do_search()
            return "break"

        def choose_suggestion(self, i):
            """A name was picked from the pop-up -> show it and open its full analysis."""
            if not (0 <= i < len(self.sugg_items)):
                return
            item = self.sugg_items[i]
            self.hide_suggestions()
            self.query.set(item["name"])
            try:
                self.entry.icursor("end")
            except Exception:  # noqa: BLE001
                pass
            self.matches = [item]
            self.filter.set("")
            self.refill()
            self.lb.selection_clear(0, "end")
            self.lb.selection_set(0)
            self.analyse()

        # ----- searching (no result limit) -----
        def do_search(self):
            self.hide_suggestions()
            text = self.query.get().strip()
            if not text:
                messagebox.showinfo("Search", "Type a company / fund name first.")
                return
            fn = (lambda: search_equities(text)) if self.kind.get() == "equity" \
                else (lambda: search_mutual_funds(text))
            self.app.run_job(fn, self.on_matches, None, f"Searching for '{text}' ...")

        def on_matches(self, results):
            self.matches = results
            self.filter.set("")
            self.refill()
            self.app.status.set(f"{len(results):,} match(es) found. Double-click one to analyse.")
            if len(results) == 1:
                self.lb.selection_set(0)
                self.analyse()

        def refill(self):
            words = self.filter.get().lower().split()
            self.shown = [m for m in self.matches
                          if all(w in (m["name"] + " " + str(m.get("ticker", ""))).lower() for w in words)]
            self.lb.delete(0, "end")
            for m in self.shown:
                self.lb.insert("end", match_label(m))
            self.count.config(text=f"Showing {len(self.shown):,} of {len(self.matches):,} matches "
                                   f"- double-click to analyse:")

        def analyse(self):
            sel = self.lb.curselection()
            if not sel:
                messagebox.showinfo("Search", "Select one item from the list first.")
                return
            m = self.shown[sel[0]]
            fn = (lambda: analyze_equity(m["ticker"], m["name"])) if "ticker" in m \
                else (lambda: analyze_fund(m["code"], m["name"]))
            self.app.run_job(fn, self.show_analysis, None, f"Analysing {m['name']} ...")

        # ----- showing the result -----
        def show_analysis(self, res):
            self.current = res
            row, is_eq = res["row"], res["kind"] == "equity"
            self.title.config(text=res["name"])
            self.subtitle.config(text=res["id"] if is_eq else f"AMFI scheme code {res['id']}")
            sbg, sfg = BADGES["Signal"].get(row.get("Signal", ""), NEUTRAL)
            self.badge.config(text=f"  {row.get('Signal', '')}  ", bg=sbg, fg=sfg)
            px = row.get("Price") if is_eq else row.get("NAV")
            self.price.config(text=(f"Rs {px:,.2f}" if is_eq else f"NAV Rs {px:,.2f}") if _isnum(px) else "")
            day = row.get("Day_%")
            dbg, dfg = return_style(day, 3)
            self.day.config(text=(f"{'▲' if day >= 0 else '▼'} {day:.2f}%") if _isnum(day) else "",
                            bg=dbg, fg=dfg)
            if is_eq:
                self.live.config(text="  connecting to live price ...  ", bg="#90a4ae", fg="white")
            else:
                self.live.config(text="  NAV is declared once a day  ", bg="#90a4ae", fg="white")
            self.upd.config(text="")
            self.watch_btn.config(state="normal" if is_eq else "disabled")

            for w in self.cards.winfo_children():
                w.destroy()
            for j, p in enumerate(PERIODS):
                t, bg, fg = cell_style(f"Ret_{p}_%", row.get(f"Ret_{p}_%"))
                card = tk.Frame(self.cards, bg=bg)
                card.grid(row=0, column=j, padx=3, sticky="nsew")
                self.cards.columnconfigure(j, weight=1)
                tk.Label(card, text=f"{p.upper()} return", bg=bg, fg=fg,
                         font=("Segoe UI", 8)).pack(padx=8, pady=(5, 0))
                tk.Label(card, text=t, bg=bg, fg=fg, font=("Segoe UI", 12, "bold")).pack(
                    padx=8, pady=(0, 5))

            for w in self.stats.winfo_children():
                w.destroy()
            for k, (label, text, bg, fg) in enumerate(build_stats(res)):
                cell = tk.Frame(self.stats, bg=bg, highlightthickness=1, highlightbackground="#d0d7de")
                cell.grid(row=k // 5, column=k % 5, padx=3, pady=3, sticky="nsew")
                self.stats.columnconfigure(k % 5, weight=1)
                tk.Label(cell, text=label, bg=bg, fg=fg, font=("Segoe UI", 8)).pack(anchor="w", padx=8, pady=(4, 0))
                tk.Label(cell, text=text[:34], bg=bg, fg=fg, font=("Segoe UI", 10, "bold")).pack(
                    anchor="w", padx=8, pady=(0, 4))

            self.panel.set_result(res)
            self.app.chart_tab.set_result(res)
            self.fill_details(res)
            self.app.status.set(f"Showing {res['name']}")
            if self._live_id is not None:
                try:
                    self.after_cancel(self._live_id)
                except Exception:  # noqa: BLE001
                    pass
                self._live_id = None
            if is_eq:
                self.live_tick()

        # ----- live price (equities only) -----
        def live_tick(self):
            self._live_id = None
            cur = self.current
            if cur is None or cur["kind"] != "equity" or not alive(self):
                return

            def done(qt, err):
                if self.current is cur and alive(self):
                    if qt:
                        self.apply_quote(qt)
                    self._live_id = self.after(15000 if is_market_open() else 60000, self.live_tick)

            bg(lambda: fetch_live_quote(cur["id"]), done)

        def apply_quote(self, qt):
            self.price.config(text=f"Rs {qt['price']:,.2f}")
            dbg, dfg = return_style(qt["pct"], 3)
            self.day.config(text=f"{'▲' if qt['change'] >= 0 else '▼'} {qt['change']:+.2f}  ({qt['pct']:+.2f}%)",
                            bg=dbg, fg=dfg)
            if qt["open"]:
                self.live.config(text="  ● LIVE  ", bg="#1f9d55", fg="white")
            else:
                self.live.config(text="  Market closed - last price  ", bg="#78909c", fg="white")
            self.upd.config(text=f"updated {qt['time']}")

        def add_watch(self):
            if self.current and self.current["kind"] == "equity":
                self.app.watch_tab.add(self.current["id"], self.current["name"])

        def save_history(self):
            if not self.current:
                return
            path = filedialog.asksaveasfilename(
                defaultextension=".csv", filetypes=[("CSV file", "*.csv")],
                initialfile=f"{str(self.current['id']).replace('.', '_')}_history.csv")
            if path:
                self.current["series"].rename("Price/NAV").to_csv(path, index_label="Date")
                messagebox.showinfo("Saved", f"Full history saved to:\n{path}")

        def fill_details(self, res):
            t = self.details
            t.delete("1.0", "end")
            if res["dividends"] is not None:
                t.insert("end", "Recent dividends\n", "head")
                if res["dividends"]:
                    t.insert("end", "   ".join(f"{d}: Rs {a:g}" for d, a in res["dividends"]) + "\n\n")
                else:
                    t.insert("end", "No dividend history found.\n\n", "muted")
            t.insert("end", "News - last 30 days (red = negative, green = positive, click to open)\n", "head")
            if not res["news"]:
                t.insert("end", "No recent news found.\n", "muted")
            for i, it in enumerate(res["news"]):
                tone = {"neg": "neg", "pos": "pos"}.get(it["tone"])
                mark = {"neg": "▼ ", "pos": "▲ "}.get(it["tone"], "• ")
                link = f"link{i}"
                t.tag_configure(link, underline=False)
                t.tag_bind(link, "<Button-1>", lambda e, u=it["link"]: webbrowser.open(u) if u else None)
                t.tag_bind(link, "<Enter>", lambda e: t.config(cursor="hand2"))
                t.tag_bind(link, "<Leave>", lambda e: t.config(cursor=""))
                tags = (tone, link) if tone else (link,)
                t.insert("end", mark + it["title"] + "\n", tags)
            t.insert("end", "\nEducational tool only - not investment advice.\n", "muted")

    # ------------------------------------------------------------------
    class ChartTab(ttk.Frame):
        """Big full-size chart of the stock / fund that was searched."""

        def __init__(self, app):
            super().__init__(app.nb, padding=8)
            self.app = app
            head = tk.Frame(self, bg=LIGHT)
            head.pack(fill="x")
            self.title = tk.Label(head, text="No chart yet - search a stock or mutual fund first",
                                  bg=LIGHT, fg=NAVY, font=("Segoe UI", 16, "bold"), anchor="w")
            self.title.pack(side="left")
            self.sub = tk.Label(head, text="", bg=LIGHT, fg="#607d8b", font=("Segoe UI", 10))
            self.sub.pack(side="left", padx=12)
            self.panel = ChartPanel(self, app, buttons=("popout", "browser"), compact=False)
            self.panel.pack(fill="both", expand=True, pady=(6, 0))

        def set_busy(self, busy):
            pass

        def set_result(self, res):
            self.title.config(text=res["name"])
            self.sub.config(text=str(res["id"]) if res["kind"] == "equity" else f"AMFI scheme {res['id']}")
            self.panel.set_result(res)

    # ------------------------------------------------------------------
    class WatchTab(ttk.Frame):
        """Live prices for your stocks / indices (auto-refresh while the market is open)."""

        HEAD = ["Name", "Last price", "Change", "Change %", "Prev close", "Day high", "Day low",
                "Volume", "Updated", ""]

        def __init__(self, app):
            super().__init__(app.nb, padding=8)
            self.app = app
            self.items = load_watchlist()
            self.quotes, self.prev = {}, {}
            self.busy = False
            self.auto = tk.BooleanVar(value=True)
            self.interval = tk.StringVar(value="15")
            self.entry = tk.StringVar()

            self.banner = tk.Label(self, text="", font=("Segoe UI", 13, "bold"), padx=12, pady=6, anchor="w")
            self.banner.pack(fill="x")
            ctl = ttk.LabelFrame(self, text=" Watchlist ", padding=8)
            ctl.pack(fill="x", pady=6)
            ttk.Label(ctl, text="Add NSE symbol / index:").pack(side="left")
            e = ttk.Entry(ctl, textvariable=self.entry, width=22)
            e.pack(side="left", padx=6)
            e.bind("<Return>", lambda ev: self.add_from_text())
            ttk.Button(ctl, text="Add", style="Accent.TButton", command=self.add_from_text).pack(side="left")
            ttk.Label(ctl, foreground="#607d8b",
                      text="  e.g. TCS, RELIANCE, ^NSEI (Nifty 50), ^NSEBANK, ^BSESN  |  or use 'Add to Watchlist' in the Search tab"
                      ).pack(side="left")
            ttk.Button(ctl, text="Refresh now", command=self.refresh).pack(side="right", padx=4)
            ttk.Combobox(ctl, textvariable=self.interval, values=["5", "10", "15", "30", "60"],
                         width=4, state="readonly").pack(side="right")
            ttk.Label(ctl, text="sec").pack(side="right", padx=(2, 8))
            ttk.Checkbutton(ctl, text="Auto-refresh every", variable=self.auto).pack(side="right")

            self.grid_frame = tk.Frame(self, bg="white")
            self.grid_frame.pack(fill="both", expand=True)
            ttk.Label(self, foreground="#78909c",
                      text="Live prices come from Yahoo Finance and can be delayed by a short time. NSE hours: "
                           "Mon-Fri 09:15-15:30 IST (exchange holidays are not detected)."
                      ).pack(anchor="w", pady=(6, 0))
            self.render()
            self.tick_clock()
            self.after(800, self.auto_loop)

        def set_busy(self, busy):
            pass

        def is_selected(self):
            try:
                return self.app.nb.select() == str(self)
            except Exception:  # noqa: BLE001
                return False

        def tick_clock(self):
            try:
                if not alive(self):
                    return
                now = ist_now()
                if is_market_open(now):
                    self.banner.config(text=f"  ● MARKET OPEN     NSE  |  {now:%a %d %b %Y  %H:%M:%S} IST",
                                       bg="#1f9d55", fg="white")
                else:
                    self.banner.config(text=f"  ● MARKET CLOSED     NSE opens Mon-Fri 09:15  |  "
                                            f"{now:%a %d %b %Y  %H:%M:%S} IST", bg="#78909c", fg="white")
                self.after(1000, self.tick_clock)
            except Exception:  # noqa: BLE001
                pass

        def auto_loop(self):
            secs = 15
            try:
                if not alive(self):
                    return
                secs = max(5, int(self.interval.get()))
                if not is_market_open():
                    secs = max(secs, 60)
                if self.auto.get() and self.is_selected():
                    self.refresh()
            except Exception:  # noqa: BLE001
                pass
            try:
                self.after(secs * 1000, self.auto_loop)
            except Exception:  # noqa: BLE001
                pass

        def refresh(self):
            if self.busy or not self.items:
                return
            self.busy = True
            tickers = [i["ticker"] for i in self.items]
            bg(lambda: fetch_many_quotes(tickers), self.on_quotes)

        def on_quotes(self, res, err):
            self.busy = False
            if res is None:
                self.app.status.set("Live refresh failed: " + str(err))
                return
            for t, qt in res.items():
                if "error" in qt:
                    self.quotes[t] = qt
                    continue
                old = self.quotes.get(t)
                self.prev[t] = old["price"] if old and "price" in old else None
                self.quotes[t] = qt
            self.render()
            self.app.status.set(f"Live prices updated at {datetime.now():%H:%M:%S}")

        def add(self, ticker, name):
            if any(i["ticker"] == ticker for i in self.items):
                self.app.status.set(f"{name} is already in the watchlist.")
                return
            self.items.append({"ticker": ticker, "name": name})
            save_watchlist(self.items)
            self.render()
            self.app.status.set(f"Added {name} to the watchlist.")
            self.refresh()

        def add_from_text(self):
            t = self.entry.get().strip().upper()
            if not t:
                return
            ticker = t if t.startswith("^") or "." in t else t + ".NS"
            self.entry.set("")

            def done(qt, err):
                if qt is None:
                    messagebox.showerror("Watchlist", f"Could not find a live price for '{ticker}'.\n{err}")
                else:
                    self.add(ticker, t.lstrip("^"))

            bg(lambda: fetch_live_quote(ticker), done)

        def remove(self, item):
            self.items = [i for i in self.items if i["ticker"] != item["ticker"]]
            save_watchlist(self.items)
            self.render()

        def open_chart(self, item):
            self.app.popup_chart_equity(item["ticker"], item["name"])

        def render(self):
            g = self.grid_frame
            for w in g.winfo_children():
                w.destroy()
            for j, h in enumerate(self.HEAD):
                tk.Label(g, text=h, bg=NAVY, fg="white", font=("Segoe UI", 9, "bold"), padx=8, pady=7,
                         width=16 if j == 0 else 11).grid(row=0, column=j, sticky="nsew", padx=(0, 1), pady=(0, 1))
            for i, it in enumerate(self.items, start=1):
                qt = self.quotes.get(it["ticker"])
                cells = [(it["name"], "#ffffff", "#0b57d0")]
                if qt and "price" in qt:
                    pbg, pfg = return_style(qt["pct"], 3)
                    old = self.prev.get(it["ticker"])
                    tick = "" if old is None or old == qt["price"] else (" ▲" if qt["price"] > old else " ▼")
                    cells += [(f"{qt['price']:,.2f}{tick}", "#ffffff", "#1b1b1b"),
                              (f"{'▲' if qt['change'] >= 0 else '▼'} {qt['change']:+.2f}", pbg, pfg),
                              (f"{qt['pct']:+.2f}%", pbg, pfg),
                              (f"{qt['prev_close']:,.2f}", "#ffffff", "#1b1b1b"),
                              (f"{qt['high']:,.2f}" if qt.get("high") else "-", "#ffffff", "#1b1b1b"),
                              (f"{qt['low']:,.2f}" if qt.get("low") else "-", "#ffffff", "#1b1b1b"),
                              (fmt_volume(qt.get("volume")), "#ffffff", "#1b1b1b"),
                              (qt["time"], "#ffffff", "#78909c")]
                elif qt:
                    cells += [("no data", "#f8c9c9", "#8b1a1a")] + [("-", "#ffffff", "#78909c")] * 7
                else:
                    cells += [("loading ...", "#ffffff", "#78909c")] + [("-", "#ffffff", "#78909c")] * 7
                for j, (txt, bg, fg) in enumerate(cells):
                    lab = tk.Label(g, text=txt, bg=bg, fg=fg, padx=8, pady=6, width=16 if j == 0 else 11,
                                   font=("Segoe UI", 10, "bold" if j in (0, 1) else "normal"),
                                   anchor="w" if j == 0 else "center")
                    if j == 0:
                        lab.config(cursor="hand2")
                        lab.bind("<Button-1>", lambda e, it=it: self.open_chart(it))
                    lab.grid(row=i, column=j, sticky="nsew", padx=(0, 1), pady=(0, 1))
                box = tk.Frame(g, bg="white")
                box.grid(row=i, column=len(cells), sticky="nsew", padx=2)
                ttk.Button(box, text="Chart", width=6, command=lambda it=it: self.open_chart(it)).pack(side="left", padx=1)
                ttk.Button(box, text="✕", width=3, command=lambda it=it: self.remove(it)).pack(side="left", padx=1)

    # ------------------------------------------------------------------
    class App(tk.Tk):
        def __init__(self):
            super().__init__()
            self.title("Stock & Mutual Fund Screener (India)")
            self.geometry("1400x900")
            self.minsize(1100, 720)
            self.configure(bg=LIGHT)
            self.running = False
            self.log_sink = None

            style = ttk.Style(self)
            try:
                style.theme_use("clam")
            except tk.TclError:
                pass
            style.configure("TNotebook.Tab", padding=(16, 8), font=("Segoe UI", 10, "bold"))
            style.map("TNotebook.Tab", background=[("selected", NAVY)],
                      foreground=[("selected", "#ffffff")])
            style.configure("Accent.TButton", background="#1f9d55", foreground="white",
                            font=("Segoe UI", 10, "bold"), padding=8)
            style.map("Accent.TButton", background=[("active", "#178a49"), ("disabled", "#9fb7a9")])

            banner = tk.Frame(self, bg=NAVY)
            banner.pack(fill="x")
            tk.Label(banner, text="Stock & Mutual Fund Screener", bg=NAVY, fg="white",
                     font=("Segoe UI", 17, "bold")).pack(side="left", padx=14, pady=10)
            tk.Label(banner, text="India  |  NSE equities & AMFI mutual funds", bg=NAVY,
                     fg="#9fb7d6", font=("Segoe UI", 10)).pack(side="left")

            bar = tk.Frame(self, bg="#e8edf3")
            bar.pack(side="bottom", fill="x")
            self.progress = ttk.Progressbar(bar, mode="indeterminate", length=160)
            self.progress.pack(side="left", padx=10, pady=6)
            self.status = tk.StringVar(value="Ready. Choose a tab, set options and press the green button.")
            tk.Label(bar, textvariable=self.status, bg="#e8edf3", fg="#37474f", anchor="w").pack(
                side="left", fill="x", expand=True)

            self.nb = ttk.Notebook(self)
            self.nb.pack(fill="both", expand=True, padx=10, pady=8)
            self.stock_tab, self.fund_tab = StockTab(self), FundTab(self)
            self.chart_tab = ChartTab(self)
            self.search_tab = SearchView(self)
            self.watch_tab = WatchTab(self)
            self.nb.add(self.stock_tab, text="  Stocks Screener  ")
            self.nb.add(self.fund_tab, text="  Mutual Funds Screener  ")
            self.nb.add(self.search_tab, text="  Search Equity / Fund  ")
            self.nb.add(self.chart_tab, text="  Chart  ")
            self.nb.add(self.watch_tab, text="  Live Watchlist  ")
            self.tabs = [self.stock_tab, self.fund_tab, self.search_tab, self.chart_tab, self.watch_tab]
            self.nb.bind("<<NotebookTabChanged>>", lambda e: self.on_tab_changed())
            self.after(100, self.poll)

        def on_tab_changed(self):
            self.search_tab.hide_suggestions()
            if self.watch_tab.is_selected():
                self.watch_tab.refresh()

        def show_chart_tab(self):
            self.nb.select(self.chart_tab)

        # ---- charts: pop-out window / browser ----
        def open_popup(self, res, rng="1Y"):
            win = tk.Toplevel(self)
            win.title(f"{res['name']} - Chart")
            win.geometry("1250x760")
            try:
                win.state("zoomed")  # Windows
            except Exception:  # noqa: BLE001
                try:
                    win.attributes("-zoomed", True)  # Linux
                except Exception:  # noqa: BLE001
                    pass
            head = tk.Frame(win, bg=NAVY)
            head.pack(fill="x")
            tk.Label(head, text=res["name"], bg=NAVY, fg="white",
                     font=("Segoe UI", 15, "bold")).pack(side="left", padx=12, pady=8)
            tk.Label(head, text=str(res["id"]), bg=NAVY, fg="#9fb7d6").pack(side="left")
            full = {"on": False}

            def toggle(_e=None):
                full["on"] = not full["on"]
                try:
                    win.attributes("-fullscreen", full["on"])
                except Exception:  # noqa: BLE001
                    pass

            ttk.Button(head, text="Full screen (F11)", command=toggle).pack(side="right", padx=10, pady=6)
            win.bind("<F11>", toggle)
            win.bind("<Escape>", lambda e: (full.update(on=False), win.attributes("-fullscreen", False)))
            panel = ChartPanel(win, self, buttons=("browser",), compact=False, initial=rng)
            panel.pack(fill="both", expand=True, padx=10, pady=8)
            panel.set_result(res)
            return win

        def open_browser(self, res):
            self.status.set("Preparing the interactive HTML chart ...")

            def build():
                intra = {}
                if res["kind"] == "equity":
                    for k in ("1D", "5D"):
                        try:
                            intra[k] = fetch_intraday(res["id"], k)
                        except Exception:  # noqa: BLE001
                            intra[k] = None
                return write_chart_html(res, intra)

            def done(path, err):
                if path:
                    webbrowser.open(Path(path).as_uri())
                    self.status.set(f"Chart opened in your browser ({path})")
                else:
                    messagebox.showerror("Chart", f"Could not create the HTML chart: {err}")

            bg(build, done)

        def popup_chart_equity(self, ticker, name):
            self.status.set(f"Loading chart for {name} ...")
            bg(lambda: load_equity_history(ticker, name), self._popup_ready)

        def popup_chart_fund(self, code, name):
            self.status.set(f"Loading chart for {name} ...")
            bg(lambda: load_fund_history(code, name), self._popup_ready)

        def _popup_ready(self, res, err):
            if res is None:
                self.status.set("Chart error: " + str(err))
                messagebox.showerror("Chart", f"Could not load the chart: {err}")
                return
            self.status.set(f"Chart ready: {res['name']}")
            self.open_popup(res)

        # ---- background jobs ----
        def run_job(self, fn, on_done, log_sink=None, msg="Working ..."):
            if self.running:
                return
            self.running, self.log_sink = True, log_sink
            self.progress.start(12)
            self.status.set(msg)
            for t in self.tabs:
                t.set_busy(True)

            def work():
                try:
                    result = fn()
                except ScreenerError as e:
                    m = str(e)
                    q.put(lambda m=m: self.job_failed(m))
                    return
                except Exception as e:  # noqa: BLE001
                    m = f"Unexpected error: {e}"
                    q.put(lambda m=m: self.job_failed(m))
                    return
                q.put(lambda: self.job_done(on_done, result))

            threading.Thread(target=work, daemon=True).start()

        def end_job(self):
            self.running = False
            self.progress.stop()
            for t in self.tabs:
                t.set_busy(False)

        def job_done(self, on_done, result):
            self.end_job()
            on_done(result)

        def job_failed(self, msg):
            self.end_job()
            self.status.set("Error: " + msg)
            messagebox.showerror("Screener", msg)

        def on_log(self, msg):
            self.status.set(msg)
            if self.log_sink:
                self.log_sink(msg)

        def poll(self):
            try:
                while True:
                    fn = q.get_nowait()
                    try:
                        fn()
                    except Exception as e:  # noqa: BLE001
                        self.end_job()
                        messagebox.showerror("Error", f"Display error: {e}")
            except queue.Empty:
                pass
            self.after(100, self.poll)

    app = App()
    LOGGER = lambda m: q.put(lambda mm=m: app.on_log(str(mm)))  # noqa: E731
    app.mainloop()
    return app


# --------------------------------------------------------------------------
# ENTRY POINT
# --------------------------------------------------------------------------
def main():
    # No arguments (e.g. double-click or "python market_screener.py") -> open the GUI
    if len(sys.argv) == 1:
        launch_gui()
        return

    p = argparse.ArgumentParser(description="Indian stock & mutual fund screener")
    sub = p.add_subparsers(dest="cmd", required=True)

    sub.add_parser("gui", help="open the graphical window").set_defaults(func=lambda a: launch_gui())

    s = sub.add_parser("stocks", help="screen shares")
    s.add_argument("--universe", choices=["nifty50", "midcap", "smallcap", "all"], default="all")
    s.add_argument("--period", choices=list(PERIODS), default="6m", help="ranking period")
    s.add_argument("--min-growth", type=float, default=None,
                   help="minimum %% return in the chosen period (e.g. 10, 20, 50)")
    s.add_argument("--top", type=int, default=10, help="how many shares to select")
    s.add_argument("--consistent", action="store_true", help="require positive 1M, 2M and 6M")
    s.add_argument("--no-news", action="store_true", help="skip news check")
    s.add_argument("--no-dividends", action="store_true", help="skip dividend check")
    s.set_defaults(func=cli_stocks)

    f = sub.add_parser("funds", help="screen mutual funds")
    f.add_argument("--query", default="flexi cap", help="e.g. 'small cap', 'nifty 50 index'")
    f.add_argument("--period", choices=list(PERIODS), default="1y")
    f.add_argument("--min-growth", type=float, default=None)
    f.add_argument("--top", type=int, default=10)
    f.add_argument("--max-funds", type=int, default=40,
                   help="how many matching schemes to scan (0 = ALL, no limit)")
    f.add_argument("--all-plans", action="store_true", help="include Regular / IDCW plans too")
    f.add_argument("--news", action="store_true", help="also check news for the top funds")
    f.set_defaults(func=cli_funds)

    args = p.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
