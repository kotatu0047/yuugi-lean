using System;
using System.Diagnostics;
using System.Text;
using System.Threading.Tasks;

namespace CardGen.App
{
    /// <summary>Lean の検査ツール（cardgen）を別のプロセスで動かし、報告を受け取る</summary>
    public static class CheckerClient
    {
        /// <summary>WSL の中の cardgen を呼ぶ既定のコマンド（最後の「-」で標準入力から読む）</summary>
        public const string DefaultCommand = "wsl.exe -e /home/yamam/repo/yuugi-lean/.lake/build/bin/cardgen -";

        /// <summary>空白で区切った最初の語をプログラム、残りを引数とする</summary>
        static (string, string) Split(string command)
        {
            var c = command.Trim();
            var i = c.IndexOf(' ');
            return i < 0 ? (c, "") : (c.Substring(0, i), c.Substring(i + 1));
        }

        public static Task<string> Run(string command, string input, int timeoutMs = 120000) => Task.Run(() =>
        {
            var (file, args) = Split(command);
            var utf8 = new UTF8Encoding(false);
            var psi = new ProcessStartInfo(file, args)
            {
                UseShellExecute = false,
                CreateNoWindow = true,
                RedirectStandardInput = true,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                StandardOutputEncoding = utf8,
                StandardErrorEncoding = utf8,
            };
            using var p = Process.Start(psi) ?? throw new InvalidOperationException($"「{file}」を起動できません");
            var stdin = new System.IO.StreamWriter(p.StandardInput.BaseStream, utf8);
            stdin.Write(input);
            stdin.Close();
            var outTask = p.StandardOutput.ReadToEndAsync();
            var errTask = p.StandardError.ReadToEndAsync();
            if (!p.WaitForExit(timeoutMs))
            {
                try { p.Kill(); } catch { }
                throw new TimeoutException("検査ツールが時間内に終わりませんでした");
            }
            var output = outTask.Result;
            if (output.Trim().Length == 0)
                throw new InvalidOperationException($"検査ツールが何も返しませんでした（終了コード {p.ExitCode}）\n{errTask.Result}");
            return output;
        });
    }
}
