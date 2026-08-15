# In-flight Oracle tasks — third-generation "standard objects" round

Pool: `company-chatgpt-pro`. Fetch with the FULL id, `2>&1`, never an 8-char prefix.
Relay-side paths are WSL-style (`/mnt/d/...`); `D:\...` is not readable from the relay.

| Paper | Task id | Dispatched | State at tick 70 |
|---|---|---|---|
| A4 `prime_languages` | `3b6b5991-740c-4e6f-bed5-d4d0a957a1cd` | tick 68 | waiting_response |
| A7 `upper_fibers` | `8ca43d8c-b3f5-4360-897a-048ba8e78d34` | tick 68 | waiting_response |
| A5 `finite_parts` | `34c44294-2678-4a31-80b7-7dae3d6c496d` | tick 70 (resend) | dispatched |
| A9 `homological_visibility` | `47eb976a-6e06-4e7a-b4d6-a2f9ed3c1ba6` | tick 70 | dispatched |

A5's first attempt `29797343-5e38-4ea8-b84b-ecbecdc18f82` died of `extraction_failure`
(worker-side scrape miss, not a protocol fault) and was resent unchanged.

Also running: A3 final revision in codex (Condition F removal, per `a3_final_task.txt`).
