# Halifax Route Lab

An interactive, mathematics-focused driving-route simulator for Halifax, Dartmouth, Bedford and Herring Cove.

[Open the published simulator](https://halifax-route-lab-math-ia.zippy-teal-0885.chatgpt.site)

This repository contains only the publishing copy. The frozen IA evidence, written exploration, and experimental records are kept separately and are not included.

## Website files

- `index.html`: interface and styling
- `app.mjs`: routing, interaction and visualization
- `graph-*.txt`: ordered chunks of the regional road graph, loaded by the application
- `robots.txt`: crawler access

Serve this directory with a static HTTP server. No build, API key or backend is required. Keep all five graph chunks beside the application module. Opening the HTML directly as a local file may block data loading; use HTTP hosting instead.

## Model

Supports Dijkstra, A*, Greedy Best-First, shortest/fastest objectives, grouped slowdowns and closures, and optional hypothetical intersection delays. Travel times are model estimates, not live traffic predictions or navigation advice.

Road data is © OpenStreetMap contributors, under ODbL. See https://www.openstreetmap.org/copyright. Original attribution is retained in the simulator. No additional software licence has been selected for this repository.
