using System.IO;
using UnityEditor;
using UnityEditor.SceneManagement;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App.EditorTools
{
    /// <summary>
    /// プロジェクトの準備とビルド。バッチモードからも呼べる：
    ///   Unity -batchmode -projectPath . -executeMethod CardGen.App.EditorTools.CardGenBuild.Setup -quit
    ///   Unity -batchmode -projectPath . -executeMethod CardGen.App.EditorTools.CardGenBuild.BuildWindows -quit
    /// </summary>
    public static class CardGenBuild
    {
        const string Dir = "Assets/CardGenEditor";
        const string ScenePath = Dir + "/Main.unity";
        const string PanelPath = Dir + "/Resources/CardGenPanelSettings.asset";
        const string ThemePath = Dir + "/Resources/CardGenTheme.tss";

        [MenuItem("CardGen/プロジェクトを準備")]
        public static void Setup()
        {
            var settings = AssetDatabase.LoadAssetAtPath<PanelSettings>(PanelPath);
            if (settings == null)
            {
                settings = ScriptableObject.CreateInstance<PanelSettings>();
                settings.themeStyleSheet = AssetDatabase.LoadAssetAtPath<ThemeStyleSheet>(ThemePath);
                settings.scaleMode = PanelScaleMode.ScaleWithScreenSize;
                settings.referenceResolution = new Vector2Int(1600, 900);
                settings.screenMatchMode = PanelScreenMatchMode.MatchWidthOrHeight;
                settings.match = 0.5f;
                AssetDatabase.CreateAsset(settings, PanelPath);
            }
            // シーンは毎回作り直す（PanelSettings の参照を確実に保存する）
            {
                var scene = EditorSceneManager.NewScene(NewSceneSetup.EmptyScene, NewSceneMode.Single);
                var cam = new GameObject("Camera").AddComponent<Camera>();
                cam.clearFlags = CameraClearFlags.SolidColor;
                cam.backgroundColor = new Color(0.13f, 0.13f, 0.14f);
                cam.tag = "MainCamera";
                var go = new GameObject("CardGen Editor");
                var doc = go.AddComponent<UIDocument>();
                var so = new SerializedObject(doc);
                so.FindProperty("m_PanelSettings").objectReferenceValue = settings;
                so.ApplyModifiedPropertiesWithoutUndo();
                go.AddComponent<CardGenApp>();
                EditorSceneManager.SaveScene(scene, ScenePath);
            }
            EditorBuildSettings.scenes = new[] { new EditorBuildSettingsScene(ScenePath, true) };
            PlayerSettings.productName = "CardGen Editor";
            PlayerSettings.companyName = "kotatu";
            PlayerSettings.fullScreenMode = FullScreenMode.Windowed;
            PlayerSettings.defaultScreenWidth = 1600;
            PlayerSettings.defaultScreenHeight = 900;
            PlayerSettings.resizableWindow = true;
            AssetDatabase.SaveAssets();
        }

        [MenuItem("CardGen/Windows 用にビルド")]
        public static void BuildWindows()
        {
            Setup();
            var report = BuildPipeline.BuildPlayer(new BuildPlayerOptions
            {
                scenes = new[] { ScenePath },
                locationPathName = "Build/CardGenEditor.exe",
                target = BuildTarget.StandaloneWindows64,
                options = BuildOptions.None,
            });
            Debug.Log($"CardGen build: {report.summary.result} ({report.summary.totalErrors} errors)");
            if (Application.isBatchMode && report.summary.result != UnityEditor.Build.Reporting.BuildResult.Succeeded)
                EditorApplication.Exit(1);
        }
    }
}
