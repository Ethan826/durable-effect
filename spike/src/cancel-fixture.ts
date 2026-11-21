// Fixture for review findings N3 and N6 (#20), on the raw Restate SDK.
// N3: after a cancelled sleep, can the handler still run journaled steps, or is the cancel signal
// reported again? N6: what does ctx.sleep do with a duration beyond u64 milliseconds?
import * as restate from "@restatedev/restate-sdk"

const describe = (error: unknown) =>
  error instanceof Error ? `${error.constructor.name}: ${error.message}` : String(error)

const fixture = restate.service({
  name: "CancelFixture",
  handlers: {
    sleepThenSample: async (ctx: restate.Context) => {
      try {
        await ctx.sleep(30_000)
        return { cancelled: false }
      } catch (error) {
        const caught = describe(error)
        const steps: Array<string> = []
        for (const name of ["sample-1", "sample-2"]) {
          try {
            const value = await ctx.run(name, () => Date.now())
            steps.push(`${name} ok ${value}`)
          } catch (again) {
            steps.push(`${name} failed: ${describe(again)}`)
          }
        }
        return { cancelled: true, caught, steps }
      }
    },
    hugeSleep: async (ctx: restate.Context) => {
      try {
        await ctx.sleep(1e20)
        return "slept"
      } catch (error) {
        return `sleep failed: ${describe(error)}`
      }
    }
  }
})

restate.serve({ services: [fixture], port: 9082 })
