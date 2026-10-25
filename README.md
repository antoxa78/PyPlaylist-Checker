# TV & Radio Playlist Checker

Desktop application for IPTV and internet-radio playlists (M3U, M3U8, PLS, XSPF,
also gzip-compressed `.m3u.gz` / `.m3u8.gz`): checks every stream, rechecks offline
ones, marks duplicates, manages groups and saves a clean playlist (logos, EPG and
player options kept). Includes a Quality column, Undo / Redo, a light or dark
theme and remembered check results between sessions.

Project page: https://github.com/antoxa78/PyPlaylist-Checker

## Highlights

* **Quality column** – resolution, video codec, frame rate and bitrate for video
  streams, and the audio format plus bitrate for radio (from the HLS playlist or
  from ffmpeg; streams that don't describe themselves need ffmpeg).
* **Remembered check results** – results are shown again when a playlist is
  opened later (in italics, with their age). Old online / offline results count as
  “not checked” when removing channels, choosing a duplicate to keep or saving a
  playlist, so a months-old result cannot silently lose a stream. They are stored
  in `results.json` under hashed keys, without addresses or logins, and are tied
  to the User-Agent / headers used for the check.
* **Undo / Redo** – Ctrl+Z and Ctrl+Y (or Ctrl+Shift+Z) reverse deleting,
  removing, renaming, moving, ticking groups, pasting and Clear list.
* **Light / dark theme** – follow the desktop, or choose Light or Dark in
  Settings → Theme.
* **Changed since the last check** – a Show filter and bold rows mark channels
  whose result changed.

## Folder contents

| Path | What it is |
|---|---|
| `playlist_checker_gui.py` | the program (single file, Python 3.9+ and Tk) |
| `bin/playlist-checker` | start command installed as `/usr/bin/playlist-checker` |
| `data/playlist-checker.desktop` | applications-menu entry (English + Hebrew) |
| `data/icons/*/playlist-checker.png`, `data/icons/scalable/playlist-checker.svg` | application icon, 16–512 px PNG and vector SVG |
| `data/playlist-checker.1` | manual page (`man playlist-checker`) |
| `data/url-list-example.txt` | example list of playlist addresses (File → Open list of playlist URLs) |
| `debian/` | Debian packaging: control, rules, changelog, copyright, install lists |
| `build-deb.sh` | builds the .deb with `dpkg-deb` only |
| `LICENSE` | MIT licence |

## Dependencies

* **Runtime** (installed automatically by apt): `python3 (>= 3.9)`, `python3-tk`
* **Recommended:** `vlc` or `mpv` (playing channels), `ffmpeg` (finds “not available in your country” banners by the picture), `fonts-dejavu-core`
* **Optional:** `culmus` (extra Hebrew fonts)
* **To build:** `dpkg-dev` (method 1), or `debhelper` + `dpkg-dev` (method 2);
  `lintian` to check the package

Works on Debian 11+, Ubuntu 22.04+, Linux Mint 21+ and other Debian-based systems.

## Build the package

### Method 1 – quick (no debhelper)

```sh
sudo apt install dpkg-dev          # usually already installed
./build-deb.sh
```

Result: `dist/playlist-checker_1.7.0_all.deb`

### Method 2 – standard Debian tools

```sh
sudo apt install debhelper dpkg-dev
dpkg-buildpackage -us -uc -b
```

Result: `../playlist-checker_1.7.0_all.deb`

## Install / remove

```sh
sudo apt install ./dist/playlist-checker_1.7.0_all.deb
playlist-checker                    # or find it in the applications menu
sudo apt remove playlist-checker
```

Use `apt install ./file.deb` (not `dpkg -i`) so the dependencies are installed too.
User settings are kept in `~/.config/playlist-checker/settings.json`; remembered check
results are in `~/.config/playlist-checker/results.json` (hashed stream keys only).

## New version

1. Change `APP_VERSION` in `playlist_checker_gui.py` (e.g. `1.7.1`).
2. Update the version in `data/playlist-checker.1` and the `.deb` file names in
   this README.
3. Add an entry at the top of `debian/changelog` with the same version
   (`dch -v 1.7.1` or by hand, keeping the exact format).
4. Run `./build-deb.sh` – it refuses to build if the program and changelog
   versions differ.
