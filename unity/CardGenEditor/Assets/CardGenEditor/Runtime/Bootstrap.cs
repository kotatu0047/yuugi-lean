using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>シーンにエディタがなければ作る（空のシーンでも動くように）</summary>
    static class Bootstrap
    {
        [RuntimeInitializeOnLoadMethod(RuntimeInitializeLoadType.AfterSceneLoad)]
        static void Create()
        {
            if (Object.FindAnyObjectByType<CardGenApp>() != null) return;
            if (Camera.main == null)
            {
                var cam = new GameObject("Camera").AddComponent<Camera>();
                cam.clearFlags = CameraClearFlags.SolidColor;
                cam.backgroundColor = new Color(0.13f, 0.13f, 0.14f);
                cam.tag = "MainCamera";
            }
            var settings = Resources.Load<PanelSettings>("CardGenPanelSettings");
            if (settings == null)
            {
                settings = ScriptableObject.CreateInstance<PanelSettings>();
                settings.themeStyleSheet = Resources.Load<ThemeStyleSheet>("CardGenTheme");
            }
            var go = new GameObject("CardGen Editor");
            var doc = go.AddComponent<UIDocument>();
            doc.panelSettings = settings;
            go.AddComponent<CardGenApp>();
        }
    }
}
